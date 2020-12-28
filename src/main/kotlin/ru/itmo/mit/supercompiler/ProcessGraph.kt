package ru.itmo.mit.supercompiler

import ru.itmo.mit.supercompiler.Generalization.Companion.generalize

/**
 * This class builds a process graph of given program 'program'
 */
class ProcessGraph(program: Program) {

    // initialize with target expression and global functions context 'where'
    private var root : Node = Node(program.expression, null)
    private var where : Where = program.where

    /**
     * Disclaimer -- a MUTABLE data structure.
     * Didn't want to work with zippers :D
     */
    private inner class Node(private var expression: Expr,
                             val parent : Node?,
                             val letSubstitution: Substitution? = null, // this is how we encode internal let substitution
                             val children : MutableList<Node> = mutableListOf(),
                             private var backedgeParent : Node? = null,
                             ) {

        val expr get() = expression // expose read only property
        val backedge get() = backedgeParent
        // also provide collection of nodes backedged by current node
        val backedged : List<Node> get() = getBackedged(this)

        fun getBackedged(to: Node) : List<Node> {
            val res = children.flatMap { getBackedged(to) }
            if (backedgeParent == to) {
                return res + setOf(this)
            }
            return res
        }

        // other Node properties
        val processed get() = backedgeParent != null // variable is processed if it has backedge
                || (expression.let{it is Constructor && it.args.isEmpty()}) // or if it is zero arity constructor
                || expression is Var // or it is LOCAL (?) variable (guess just Var, not Fun)
        val trivial get() = !expression.isNontrivial()

        tailrec fun Expr.isNontrivial() : Boolean {
            when (this) {
                is Function -> return false
                is Case ->
                    if (match.asVariableApplications() != null) {
                        return true // if matching something indestructable, it is nontrivial
                    } else {
                        return match.isNontrivial() // con := case con of ...
                    }
                is Application -> return lhs.isNontrivial() // con := con e
                else -> return true // trivial in other cases
            }
        }

        /**
         * extracts next unprocessed node
         */
        fun next() : Node? {
            for (ch in children) {
                ch.next()?.let { return it } // DFS
            }
            return null
        }

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
            children.clear()
            children.addAll(expression.driveRec())
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
                    asVariableApplications()?.let { lst -> return lst.map { e -> Node(e, this@Node)} }
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
        private fun Expr.asVariableApplications() : List<Expr>? {
            return when (this) {
                is Application -> lhs.asVariableApplications()?.plus(rhs)
                is Var -> listOf(this)
                else -> null
            }
        }

        /**
         * This function replaces node n with expression e
         *
         * the nodeBuilder takes parent node as an argument
         */
        fun replace(old : Node, nodeBuilder : (Node?) -> Node) : Boolean {
            if (old == this) {
                if (parent == null) error("Parent should be not null")
                // uhh, ugly
                val id = parent.children.indexOf(old)
                parent.children.removeAt(id)
                parent.children.add(id, nodeBuilder(this))
                return true
            }
            for (n in children) {
                if (n.replace(old, nodeBuilder)) {
                    return true
                }
            }
            return false
        }

        /**
         * Returns first ancestor that satisfies bi-argument predicate
         * The first argument is expression from uppermost node, the second argument is from bottommost node
         */
        fun ancestor(predicate : (Expr, Expr) -> Boolean) : Node? {
            val res = parent
            while (res != null) {
                if (predicate(res.expression, expression)) return res
            }
            return null
        }

        // folds e2 expression to the receiver
        infix fun fold(e2 : Node) {
            e2.backedgeParent = this
        }

    }

    /**
     * Replaces node 'n' in the tree (by ref) with fresh node with expression e
     */
    private fun replace(old : Node, nodeBuilder : (Node?) -> Node) : Boolean {
        if (old == root) {
            root = nodeBuilder(null)
            return true
        }
        return old.replace(old, nodeBuilder)
    }

    /**
     * Performs abstraction of node 'alpha' with respect to node 'beta'
     */
    private fun abstract(alpha : Node, beta : Node) {
        val generalization = generalize(alpha.expr, beta.expr)
        replace(alpha) { p -> Node(generalization.expr, p, generalization.subLeft) }
    }

    /**
     * The most important function: builds process tree of the program
     * Returns amount of steps just for curiosity
     */
    private fun buildProcessTree() : Int {
        var i = 0
        while (true) {
            val processing = root.next() ?: return i // end function when no processing nodes left
            i++

            if (processing.trivial) {
                processing.drive()
                continue
            }

            val renamingAncestor = processing.ancestor { ancestor, proc -> ancestor isomorphic generalize(ancestor, proc).expr }
            if (renamingAncestor != null) {
                renamingAncestor.fold(processing)
                continue
            }

            val substAncestor = processing.ancestor{ ancestor, proc -> ancestor isomorphic proc}
            if (substAncestor != null) {
                abstract(processing, substAncestor)
                continue
            }

            val whistleAncestor = processing.ancestor {ancestor, proc -> proc homoCoupling ancestor}
            if (whistleAncestor != null) {
                abstract(whistleAncestor, processing)
                continue
            }

            processing.drive()
        }
    }

}