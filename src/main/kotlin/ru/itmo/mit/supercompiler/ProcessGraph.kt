package ru.itmo.mit.supercompiler

/**
 * This class builds a process graph of given program 'program'
 */
class ProcessGraph(program: Program) {


    private var root : Node = Node(program.expression, null)
    private var where : Where = program.where

    /**
     * Disclaimer -- a MUTABLE data structure.
     * Didn't want to work with zippers :D
     */
    private inner class Node(private var expression: Expr,
                             val parent : Node?,
                             val letSubstitution: Substitution? = null, // this is how we encode internal let substitution
                             var children : List<Node> = listOf(),
                             val backedgeParent : Node? = null,
                             val backedgeChildren : MutableList<Node> = mutableListOf(),
                             ) {

        val expr get() = expression // expose read only property (don't let mutate the state outside class)

        /**
         * A mutable fmap function, modifies storing expression
         * Returns itself as chaining
         */
        private fun fmapExpr(f : Expr.() -> Expr) : Node {
            expression =  f (expression)
            return this
        }

        /**
         * The function performs driving ands saves result to the children variable
         */
        fun drive() {
            children = expression.driveRec()
        }

        /**
         * This function slightly reminds the beta reduction rule
         * But! This is not recursive function, it tries to make simultaneous
         * reductions at once, memoizing intermediate expressions at children nodes when necessary
         * And when it can do reduction does it
         */
        private fun Expr.driveRec() : List<Node> {
            // separately process nodes with artificial let substitution
            if (letSubstitution != null) {
                return listOf(Node(expression, this@Node)) + letSubstitution.values.map { Node(it, this@Node) }
            }
            // observables
            when (this) {
                // 1. local variable
                // 2. or multiple applications to local variable:
                is Application -> {
                    // look up for head, if it is variable in head position, fold arguments to the list
                    collectApplications()?.let { lst -> return lst.map { e -> Node(e, this@Node)} }
                }
                // 3. or constructor
                is Constructor -> return args.map {Node(it, this@Node)}
                // 4. or lambda abstraction
                is Lambda -> return listOf(Node(body, this@Node))
            }
            // otherwise, process reduction in context
            return listOf(driveBetaReduction() ?: error("Cannot do reduction in driving. Maybe the term is invalid?"))
        }

        /**
         * driving with context reductions -- reminds beta reduction
         * this reductions are usually transition compressed before yielding the final program
         * @see ru.itmo.mit.supercompiler.Program.whnfBetaReduction
         */
        private fun Expr.driveBetaReduction() : Node? {
            return when (this) {
                is Function -> Node(where[name] ?: error("No such global $name"), this@Node)
                is Application -> {
                    if (lhs is Lambda) {
                        // con<(\v -> body) @ rhs>   =>   con< body {v := rhs} >
                        return lhs.body.substituteVar(Var(lhs.name), rhs).let { Node(it, this@Node) }
                    } else {
                        // maybe redex in lhs according to 'con := con e' rule
                        return lhs.driveBetaReduction()?.let { it.fmapExpr { Application(it.expression, rhs) } }
                    }
                }
                is Case ->
                    // 'con := case con of ...
                    match.driveBetaReduction()?.let{ it.fmapExpr { Case(it.expression, branches) } }
                    // con<case (C ve) of ... (C p) -> e esac>   =>   con<e{p \\ ve}>
                    ?: branches.find { (p, _) -> p.cover(match) }
                        ?.let { (p, e) -> p.substitutionData(match)?.fold(e) {acc, (v, b) -> acc.substituteVar(v, b)} }
                        ?.let { Node(it, this@Node) }
                else -> null
            }

        }

        /**
         * This function collects applications to single list if there is
         * a variable in the head position. In other case it returns null
         */
        private fun Expr.collectApplications() : List<Expr>? {
            return when (this) {
                is Application -> lhs.collectApplications()?.plus(rhs)
                is Var -> listOf(this)
                else -> null
            }
        }

    }

}