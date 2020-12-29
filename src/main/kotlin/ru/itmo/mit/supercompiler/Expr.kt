package ru.itmo.mit.supercompiler

import ru.itmo.mit.supercompiler.Constructor.Companion.fls
import ru.itmo.mit.supercompiler.Constructor.Companion.num
import ru.itmo.mit.supercompiler.Constructor.Companion.tru
import ru.itmo.mit.supercompiler.Generator.numberedVariables

enum class Assoc {LEFT, RIGHT, NONE, IGNORE}

/**
 * Represents expression of our language
 */
sealed class Expr(open val priority : Int, open val assoc : Assoc, open val leaf : Boolean) {

    var parent : Expr? = null

    protected fun placeBracketsWhenShow(contextPosition : Assoc, expression: Expr) : String {
        return placeBracketsWhenShow(priority, contextPosition, expression)
    }

    companion object {
        fun placeBracketsWhenShow(contextPriority : Int, contextPosition : Assoc, expression: Expr) : String {
            if (expression.priority < contextPriority) { // lesser priority -- should put brackets
                return "($expression)"
            }
            // equal priority
            if (expression.priority == contextPriority) {
                if (expression.assoc == contextPosition && (contextPosition == Assoc.LEFT || contextPosition == Assoc.RIGHT)) {
                    return "$expression"
                }
                // use ignore for lists
                if (contextPosition == Assoc.IGNORE) {
                    return "$expression"
                }
                return "($expression)"
            }
            return "$expression"
        }
    }

    /**
     * Проверям, являются ли термы равными с точностью до имён замкнутых переменных
     */
    infix fun isomorphic(other : Expr) = renamedBoundVariables().equals(other.renamedBoundVariables())

    /**
     * Переименование замкнутых переменных
     * :parameter `nameBanList` -- какие имена не следует генерировать
     */
    fun renamedBoundVariables(prefix : String = "x", nameBanList : Set<String> = setOf()) : Expr {
        return renameWithContext(numberedVariables(prefix,nameBanList + freeVars).iterator(), mapOf())
    }

    /**
     * Переименование замкнутых переменных с генератором имён
     */
    public fun renameWithContext(nameGenerator : Iterator<String>) = renameWithContext(nameGenerator, mapOf())

    /**
     * Переименование замкнутых переменных с генератором имён и контекстом переименования
     */
    private fun renameWithContext(nameGenerator : Iterator<String>, renaming : Map<String, String>) : Expr {
        return when (this) {
            is Var -> renaming[name] ?.let { Var(it) } ?: this // globals doesn't rename
            is Constructor -> Constructor(name, args.map { it.renameWithContext(nameGenerator, renaming) })
            is Function -> this // global function references doesn't rename either
            is Lambda -> {
                val nextName = nameGenerator.next() // and every variable in new scope gets renamed
                Lambda(nextName, body.renameWithContext(nameGenerator, renaming + Pair(name, nextName)))
            }
            is Application -> Application(lhs.renameWithContext(nameGenerator, renaming), rhs.renameWithContext(nameGenerator, renaming))
            is Case -> Case(match.renameWithContext(nameGenerator, renaming),
                            branches.map { (p, e) ->
                                val localRenaming = p.args.associate { Pair(it.name, nameGenerator.next()) }
                                Pair(
                                    Pattern(p.name, p.args.map { Var(localRenaming[it.name] ?: "") }),
                                     e.renameWithContext(nameGenerator, renaming + localRenaming))
                            })
            is Let -> {
                Let(name, // DO NOT change the name of let-binding
                    definition.renameWithContext(nameGenerator, renaming),
                    body.renameWithContext(nameGenerator, renaming))
            }

        }
    }

    val freeVars by lazy { getFreeVariables() }
    fun getFreeVariables() : Set<String> {
        return when (this) {
            is Var -> setOf(name)
            is Constructor -> args.map (Expr::getFreeVariables).fold(setOf(), { b, a -> a + b})
            is Function -> setOf()
            is Lambda -> body.getFreeVariables() - name
            is Application -> lhs.getFreeVariables() + rhs.getFreeVariables()
            is Case -> match.getFreeVariables() + branches.map { (p, e) -> e.getFreeVariables() - p.args.map { it.name } }
                                                       .fold(setOf(), {b, a -> a + b})
            is Let ->  definition.getFreeVariables() + (body.getFreeVariables() - name)
        }
    }

    val boundVars by lazy { boundVariables() }
    fun boundVariables() : Set<String> {
        return when (this) {
            is Var -> setOf()
            is Constructor -> args.map (Expr::boundVariables).fold(setOf(), { b, a -> a + b})
            is Function -> setOf()
            is Lambda -> setOf(name) + body.boundVariables()
            is Application -> lhs.boundVariables() + rhs.boundVariables()
            is Case -> match.boundVariables() + branches.map { (p, e) ->  e.boundVariables() + p.args.map { it.name } }
                .fold(setOf(), {b, a -> b + a})
            is Let -> definition.boundVariables() + body.boundVariables() - name
        }
    }

    /**
     * Теперь мы даже можем проверять, является ли терм валидным для суперкомпиляции
     */
    fun isValid() : Boolean = freeVars.intersect(boundVars).isEmpty()


    fun substituteVar(what : Var, with : Expr) : Expr {
        if (!isValid() || !what.isValid() || !with.isValid()) {
            error("You can use substitude only with valid terms!")
        }
        return substituteVarUnsafe(what, with)
    }

    fun substituteVar(what : Var, with : Expr, gen : Iterator<String>) : Expr {

        if (!what.isValid() || !with.isValid()) {
            error("You can use substitude only with valid terms!")
        }
        if (!isValid()) {
            this.renameWithContext(gen).substituteVarUnsafe(what, with)
        }
        return substituteVarUnsafe(what, with)
    }

    private fun substituteVarUnsafe(what : Var, with : Expr) : Expr {
        if (equals(what)) return with
        return when (this) {
            is Var -> if (name == what.name) with else this
            is Constructor -> Constructor(name, args.map {it.substituteVar(what, with)})
            is Function -> this
            is Lambda -> Lambda(name, body.substituteVar(what, with))
            is Application -> Application(lhs.substituteVar(what, with), rhs.substituteVar(what, with))
            is Case -> Case(match.substituteVar(what, with), branches.map { (p, e) -> Pair(p, e.substituteVar(what, with))})
            is Let -> Let(name, definition.substituteVar(what, with), body.substituteVar(what, with))
        }
    }
}

// case classes:
data class Var(val name : String) : Expr(10, Assoc.NONE, true) {
    init {
        if (!name[0].isLowerCase()) {
            throw RuntimeException("variable names should begin with lowercase letter")
        }
    }
    override fun toString() = name
}

class Constructor private constructor(val name : String, val args : List<Expr>, priority: Int, assoc: Assoc, leaf: Boolean)
    : Expr(priority, assoc, leaf) {

    override fun equals(other: Any?): Boolean {
        if (other is Constructor) {
            return name == other.name && args.equals(other.args)
        }
        return super.equals(other)
    }

    override fun hashCode(): Int {
        return name.hashCode() + 371 * args.hashCode()
    }

    constructor(name : String) : this(name, listOf())

    constructor(name : String, args : List<Expr>)
    : this(name, args, 9, Assoc.NONE, args.isEmpty())

    companion object {
        infix fun Expr.cons(other : Expr) = Constructor("Cons", listOf(this, other), 3, Assoc.LEFT, false)
        val nil = Constructor("Nil", listOf(), 10, Assoc.NONE, true)

        fun Expr.succ() = Constructor("S", listOf(this))
        val zero = Constructor("Z", listOf())
        fun num(n : Int) : Constructor = if (n == 0) zero else (num(n-1).succ())

        val tru = Constructor("True", listOf())
        val fls = Constructor("False", listOf())
    }
    init {
        // check constructor name.
        if (name == "Cons" && args.size != 2)  throw error("List constructor can only have two parameters")
        if (name == "Nil" && args.size != 0)  throw error("Empty list constructor has no parameters")
        if (name == "S" && args.size != 1)  throw error("Church successor constructor 'S' accepts only one argument")
        if (name == "Z" && args.size != 0)  throw error("Church zero constructor 'Z' accepts no argument")
        if (name == "True" && args.size != 0)  throw error("Booleans constructors have no parameters")
        if (name == "False" && args.size != 0)  throw error("Boolean constructors have no parameters")
        if (!name[0].isUpperCase()) {
            throw RuntimeException("Data constructors should begin with capital letter")
        }
        // parent reassignment
        args.forEach{it.parent = this}
    }

    fun asChurchNumeral() : Int? {
        if (name == "S" && args.size == 1) {
            val of = args[0]
            if (of is Constructor) {
                return of.asChurchNumeral()?.let { it + 1 }
            }
        }
        if (name == "Z" && args.isEmpty()) return 0
        return null
    }

    override fun toString() : String {
        if (name == "Cons") {
            return "${placeBracketsWhenShow(Assoc.IGNORE, args.get(0))} : ${placeBracketsWhenShow(Assoc.IGNORE, args.get(1))}"
        } else if (name == "Nil") {
            return "[]"
        }
        val tryAsChurch = asChurchNumeral()
        if (tryAsChurch != null) {
            return "$tryAsChurch"
        }
        return "$name ${args.map { placeBracketsWhenShow(Assoc.NONE, it) }.joinToString(" ")}"
    }
}

data class Function(val name : String) : Expr(10, Assoc.NONE,true) {

    companion object {
        val sumFname = "+"
        val mulFname = "*"
        val leqFname = "<"

        fun Expr.evalBuiltinApplication() : Expr? {
            val (head, applicands) = asApplicationList()
            if (head is Function && head.builtin) {
                if (applicands.size == 2) {
                    val (e1, e2) = applicands
                    if (!(e1 is Constructor && e2 is Constructor)) return null
                    val v1 = e1.asChurchNumeral() ?: return null
                    val v2 = e2.asChurchNumeral() ?: return null

                    return when (head.name) {
                        sumFname -> num(v1 + v2)
                        mulFname -> num(v1 * v2)
                        leqFname -> if (v1 < v2) tru else fls
                        else -> return null
                    }
                }
            }
            return null
        }


        infix fun Expr.plus(other : Expr) = Function(sumFname).app(this).app(other)
        infix fun Expr.mult(other : Expr) = Function(mulFname).app(this).app(other)
        infix fun Expr.leq(other : Expr)  = Function(leqFname).app(this).app(other)
    }

    val builtin = name in listOf("+", "*", "<")
    override fun toString() = name




}

data class Lambda(val name : String, val body : Expr) : Expr(0, Assoc.RIGHT, false) {
    init {
        body.parent = this
    }
    // no need to put brackets, lowest priority
    override fun toString() = "\\$name . ${placeBracketsWhenShow(Assoc.IGNORE, body)}"
}

data class Application(val lhs : Expr, val rhs : Expr) : Expr(9, Assoc.LEFT,false) {
    init {
        lhs.parent = this
        rhs.parent = this
    }
    override fun toString() : String {
        return "${placeBracketsWhenShow(priority, Assoc.LEFT, lhs)} ${placeBracketsWhenShow(priority, Assoc.RIGHT, rhs)}"
    }
}
data class Case(val match : Expr, val branches : List<Pair<Pattern, Expr>>) : Expr(10, Assoc.NONE, false) {
    init {
        match.parent = this
        branches.forEach{(_, e) -> e.parent = this}
    }
    override fun toString(): String {
        return "case ${match} of ${branches.map {(p, b) -> "$p -> $b"}.joinToString(";\n    ", "\n    ", ";\n") }esac"
    }
}
data class Let(val name : String, val definition : Expr, val body : Expr) : Expr(10, Assoc.RIGHT, false) {
    init {
        definition.parent = this
        body.parent = this
    }
    override fun toString(): String = "let $name=$definition in ${placeBracketsWhenShow(Assoc.RIGHT, body)}"
}


/**
 * Pattern is not an expression, but it is a part of 'Case' statement
 */
data class Pattern(val name : String, val args : List<Var>) {
    companion object {
        val patNil = Pattern("Nil", listOf())
        fun patCons(vararg vars : String) = Pattern("Cons", vars.map { Var(it) })
        val patZero = Pattern("Z", listOf())
        fun patSuc(vname: String) = Pattern("S", listOf(Var(vname)))
        val patTrue = Pattern("True", listOf())
        val patFalse = Pattern("False", listOf())
    }
    init {
        // check constructor name
        Constructor(name, args)
    }

    /**
     * Check that patterns are matching the same
     */
    infix fun match(other : Pattern) = name == other.name && args.size == other.args.size

    override fun toString() = Constructor(name, args).toString()

    /*
     Check if expression is covered by this pattern
     */
    fun cover(expr : Expr) : Boolean {
        if (expr is Constructor) {
            return expr.name == name && expr.args.size == args.size
        }
        return false
    }

    fun substitutionData(ctor : Expr) : List<Pair<Var, Expr>>? {
        if (!(ctor is Constructor)) return null
        if (ctor.name != name || args.size != ctor.args.size) return null
        return args.zip(ctor.args)
    }

}