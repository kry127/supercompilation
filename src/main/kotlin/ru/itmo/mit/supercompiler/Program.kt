package ru.itmo.mit.supercompiler

import ru.itmo.mit.supercompiler.Function.Companion.evalBuiltinApplication

/**
 * Мы рассматриваем программу как корневое выражение с определёнными в контексте функциями
 */
class Program private constructor(val expression: Expr, val where: Where) {

    companion object {

        /**
         * Use this function to convert expression to program
         * All globals added to the expression as letRec expressions
         */
        private fun Expr.infiltrateGlobals(globals : Map<String, Expr>) : Expr {
            return globals.entries.fold(this) { e, (fname, fdef) -> Let(fname, fdef, e)}
        }
        /**
         * Use this function to convert expression to program
         * where all 'letrec' constructions have been moved to 'where' context
         */
        fun convertToProgram(expression: Expr,
                             globals : Map<String, Expr> = mapOf(),
                             variablePrefix : String = "p") : Program {
            val ctx = mutableMapOf<String, Expr>()
            fun Expr.visitor() : Expr {
                return when(this) {
                    is Let -> {
                        if (name in ctx) {
                            val newName = Generator.numberedVariables(name) { !(it in ctx) }.first()
                            ctx += newName to definition
                            // substitute function name
                            body.substitudeFunName(name, newName).visitor()
                        } else {
                            ctx += name to definition
                            body.visitor()
                        }
                    }
                    is Application -> Application(lhs.visitor(), rhs.visitor())
                    is Lambda -> Lambda(name, body.visitor())
                    is Case -> Case(match.visitor(), branches.map { (p, e) -> p to e.visitor() })
                    is Constructor -> Constructor(name, args.map { e -> e.visitor() })
                    else -> this
                }
            }
            val preparedExpression = expression.infiltrateGlobals(globals).renamedBoundVariables(variablePrefix)
            return Program(preparedExpression.visitor(), ctx.toMap())
        }

        fun Expr.substitudeFunName(from : String, to : String) : Expr {
            return when (this) {
                is Var -> this
                is Constructor -> Constructor(name, args.map {it.substitudeFunName(from, to)})
                is Function -> if (name == from) Function(to) else this
                is Lambda -> Lambda(name, body.substitudeFunName(from, to))
                is Application -> Application(lhs.substitudeFunName(from, to), rhs.substitudeFunName(from, to))
                is Case -> Case(match.substitudeFunName(from, to), branches.map { (p, e) -> Pair(p, e.substitudeFunName(from, to))})
                is Let -> {
                    val newBody = if (name == from) body else body.substitudeFunName(from, to)
                    Let(name, definition.substitudeFunName(from, to), newBody)
                }
            }
        }
    }

    val funcVars by lazy { where.keys }

    fun renamedBoundVariables(prefix : String = "x") = Program(
        expression, where.mapValues {(name, body) -> body.renamedBoundVariables(prefix, expression.freeVars + funcVars + name)}
    )

    fun toExpr() = where.entries.fold (expression) {e, (f, b) -> Let(f, b, e) }

    override fun toString(): String {
        if (where.isEmpty()) {
            return "$expression"
        }
        return """$expression
            | where
            |  ${where.map { (k, v) -> "$k = $v" }.joinToString("  ", "\n  ", "\n")}
        """.trimMargin()
    }

    fun fmap(f : Expr.() -> Expr) : Program {
        return Program(f (expression), where)
    }

    /*
     * This function extracts one let definition to where block if possible
     */
    fun extractLetRec() : Program? {
        return expression.extractLetRec()
    }
    private fun Expr.extractLetRec() : Program? {
        when (this) {
            // not extractable:
            is Var -> return null
            is Function -> return null

            is Lambda -> return body.extractLetRec()?.fmap{ Lambda(name, this) }
            is Application -> return lhs.extractLetRec()?.fmap{ Application(this, rhs) }
                                  ?: rhs.extractLetRec()?.fmap{ Application(rhs, this) }
            is Constructor ->  {
                for (i in args.indices) {
                    val res = args[i].extractLetRec()
                    if (res != null) {
                        val argsMutable = args.toMutableList()
                        argsMutable[i] = res.expression
                        return Program(Constructor(name, argsMutable), res.where)
                    }
                }
               return null
            }
            is Case -> return match.extractLetRec() ?: branches.map { (_, b) -> b.extractLetRec() }.filter{ it != null }.firstOrNull()


            is Let -> return Program(body, where + (name to definition))
        }
    }

    /*
     * One step reduction for program
     */
    fun whnfBetaReduction(withBuiltins : Boolean = true) : Program? {
        return expression.whnfBetaReduction(withBuiltins)
    }
    private fun Expr.whnfBetaReduction(withBuiltins : Boolean) : Program? {
        return when (this) {
            // not reducible:
            is Var -> return null
            is Constructor -> return null
            is Lambda -> return null

            // try to extract let expression
            is Let -> this.extractLetRec()

            is Function -> where[name]?.let { Program(it, where) } // unfold

            is Application -> {
                if (withBuiltins) {
                    evalBuiltinApplication()?.let{return Program(it, where)} // try to eval builtin
                }
                if (lhs is Lambda) {
                    return lhs.body.substituteVar(Var(lhs.name), rhs).let { Program(it, where) }
                } else {
                    return lhs.whnfBetaReduction(withBuiltins)?.let { Program(Application(it.expression, rhs), where) }
                }
            }
            is Case -> match.whnfBetaReduction(withBuiltins)?.let{ Program(Case(it.expression, branches), where) }
                ?: branches.find { (p, _) -> p.cover(match) }
                    ?.let { (p, e) -> p.substitutionData(match)?.fold(e) {acc, (v, b) -> acc.substituteVar(v, b)} }
                    ?.let { Program(it, where) }
        }
    }

    fun hnfBetaReduction(withBuiltins : Boolean = true) : Program? {
        return expression.hnfBetaReduction(withBuiltins)
    }
    private fun Expr.hnfBetaReduction(withBuiltins : Boolean) : Program? {
        return when (this) {
            // not reducible:
            is Var -> return null

            // try to extract let expression
            is Let -> this.extractLetRec()

            is Lambda -> body.hnfBetaReduction(withBuiltins)?.let { Program(Lambda(name, it.expression), where) }
            is Constructor -> {
                for (i in args.indices) {
                    val res = args[i].hnfBetaReduction(withBuiltins)
                    if (res != null) {
                        val argsMutable = args.toMutableList()
                        argsMutable[i] = res.expression
                        return Program(Constructor(name, argsMutable), res.where)
                    }
                }
                return null
            }

            is Function -> where[name]?.let { Program(it, where) }

            is Application -> {
                if (withBuiltins) {
                    evalBuiltinApplication()?.let{return Program(it, where)} // try to eval builtin
                }
                if (lhs is Lambda) {
                    return lhs.body.substituteVar(Var(lhs.name), rhs).let { Program(it, where) }
                } else {
                    return lhs.hnfBetaReduction(withBuiltins)?.let { Program(Application(it.expression, rhs), where) }
                        ?: rhs.hnfBetaReduction(withBuiltins)?.let { Program(Application(lhs, it.expression), where) }
                }
            }
            is Case -> match.hnfBetaReduction(withBuiltins)?.let{ Program(Case(it.expression, branches), where) }
                ?: branches.find { (p, _) -> p.cover(match) }
                    ?.let { (p, e) -> p.substitutionData(match)?.fold(e) {acc, (v, b) -> acc.substituteVar(v, b)} }
                    ?.let { Program(it, where) }
        }
    }

    /**
     * Reduce program with strategy
     * Specify withBuiltins boolean parameter to
     */
    fun nfWith(withBuiltins : Boolean = true, strategy : Program.(Boolean) -> Program?) : Program {
        var prev = this
        var e: Program?
        while (true) {
            e = prev.strategy(withBuiltins) ?: return prev
            prev = e
        }
    }

    fun whnf() : Program = nfWith { whnfBetaReduction(true) }
    fun hnf() : Program = nfWith { hnfBetaReduction(true) }

    /**
     * Produce sequence of reductions
     */
    fun whnfSeq() : Sequence<Program> = generateSequence (this) { it.whnfBetaReduction(true) }
    fun hnfSeq() : Sequence<Program> = generateSequence (this) { it.hnfBetaReduction(true) }

    fun whnf_noBuiltins() : Program = nfWith { whnfBetaReduction(false) }
    fun hnf_noBuiltins() : Program = nfWith { hnfBetaReduction(false) }
    fun whnfSeq_noBuiltins() : Sequence<Program> = generateSequence (this) { it.whnfBetaReduction(false) }
    fun hnfSeq_noBuiltins() : Sequence<Program> = generateSequence (this) { it.hnfBetaReduction(false) }


}