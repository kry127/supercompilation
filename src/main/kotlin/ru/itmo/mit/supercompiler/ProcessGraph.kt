package ru.itmo.mit.supercompiler

import ru.itmo.mit.supercompiler.Generalization.Companion.generalize

/**
 * This class builds a process graph of given program 'program'
 * To use this class use 'supercompile' static method
 */
class ProcessGraph private constructor(program: Program) {

    // don't let them build this monster, just give them simple interface:
    companion object {
        fun supercompile(program: Program) : Program {
            val pg = ProcessGraph(program)
            return pg.extractProgram().toProgram(program.where)
        }
    }

    // initialize with target expression and global functions context 'where'
    private var root : Node = Node(program.expression, null)
    private val where : Where = program.where
    // initialize set of unprocessed nodes
    private val unprocessed : MutableSet<Node> = mutableSetOf()
    // and even initialize proper names generator, so no collisions occur
    private val nameGen = Generator.numberedVariables("s",
        program.expression.boundVars + program.expression.freeVars + where.keys).iterator()

    init {
        // after that, initialization continues with building process tree (potentially infinite process)
        buildProcessTree()
        // now the class is ready for program extraction
    }

    /**
     * Disclaimer -- a MUTABLE data structure.
     * Didn't want to work with zippers :D
     */
    private inner class Node(private var expression: Expr,
                             val parent : Node?,
                             val letSubstitution: Substitution? = null, // this is how we encode internal let substitution
                             val children : MutableList<Node> = mutableListOf(),
                             var childrenPat : List<Pattern>? = null, // if it is nontrivial pattern, this is not null
                             private var backedgeParent : Node? = null,
                             private val transition : Boolean = false,
                             ) {
        init {
            // place yourself in unprocessed list :)
            unprocessed.add(this)
        }

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

        val nontrivial_func = expression.isNontrivial().first
        val nontrivial_case = expression.isNontrivial().second
        val nontrivial = expression.isNontrivial().let { it.first || it.second }
        val trivial = !nontrivial

        tailrec fun Expr.isNontrivial() : Pair<Boolean, Boolean> {
            when (this) {
                is Function -> return true to false
                is Case ->
                    if (match.asVariableApplications() != null) {
                        return false to true // if matching something indestructable, it is nontrivial
                    } else {
                        return match.isNontrivial() // con := case con of ...
                    }
                is Application -> return lhs.isNontrivial() // con := con e
                else -> return false to false // trivial in other cases
            }
        }

        /**
         * A mutable fmap function, modifies storing expression
         * Returns itself as chaining
         */
        private fun fmapExpr(f : Expr.() -> Expr) : Node {
            expression =  f (expression)
            return this
        }

        /// DRIVING
        /**
         * The function performs driving ands saves result to the children variable
         */
        fun drive() {
            if (!children.isEmpty()) error("The node have been driven twice!")
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
                is Let -> error ("Whoa, cannot process Let expression because I consider target expression from Program")
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
            driveBetaReduction()?.let { return listOf(it) }
            // otherwise, process nontrivial case
            nonTrivialCase()?.let { (head, branches) ->
                childrenPat = branches.map { (p, _) -> p} // we make this nontrivial case node, so remember patterns
                listOf(head) + branches.map { (_, e) -> e } // return all collected nodes + head node
            }
            error("Driving exhausted. Maybe the term is invalid?")
        }

        /**
         * driving with context reductions -- reminds beta reduction
         * this reductions are usually transition compressed before yielding the final program
         * @see ru.itmo.mit.supercompiler.Program.whnfBetaReduction
         */
        private fun Expr.driveBetaReduction() : Node? {
            when (this) {
                is Function -> return Node(where[name] ?: error("No such global $name"), this@Node, transition = true)
                is Application -> {
                    if (lhs is Lambda) {
                        // con<(\v -> body) @ rhs>   =>   con< body {v := rhs} >
                        return lhs.body.substituteVar(Var(lhs.name), rhs).let { Node(it, this@Node, transition = true) }
                    } else {
                        // maybe redex in lhs according to 'con := con e' rule
                        return lhs.driveBetaReduction()?.let { it.fmapExpr { Application(it.expression, rhs) } }
                    }
                }
                is Case -> {
                    // 'con := case con of ...
                    match.driveBetaReduction()?.let { return it.fmapExpr { Case(it.expression, branches) } }
                    // con<case (C ve) of ... (C p) -> e esac>   =>   con<e{p \\ ve}>
                    branches.find { (p, _) -> p.cover(match) }
                        ?.let { (p, e) ->
                            p.substitutionData(match)?.fold(e) { acc, (v, b) -> acc.substituteVar(v, b) }
                        }
                        ?.let { return Node(it, this@Node, transition = true) }
                }
            }
            return null
        }

        /**
         * Extracts a nontrivial head expression and list of branches
         */
        private fun Expr.nonTrivialCase() : Pair<Node, List<Pair<Pattern, Expr>>>? {

            fun rewrapToContext(what : Pair<Node, List<Pair<Pattern, Expr>>>,
                                wrapper : (Expr) -> Expr)
             : Pair<Node, List<Pair<Pattern, Expr>>> {
                val (head, branches) = what
                return head to branches.map { (p, e) -> p to wrapper(e)}
            }

            // nontrivial case...
            when (this) {
                is Case -> {
                    val varApp = match.asVariableApplications()
                    if (varApp != null) {

                        return Pair(
                            Node(match, this@Node), // the node we match
                                branches // the patterns we consider (WARN: we don't rename them, because local names are distinct)
                        )
                    } else {
                        // con := case con of ...
                        return match.nonTrivialCase()?.let { rewrapToContext(it) { e -> Case(e, branches) } } // rewrap
                    }
                }
                is Application -> {
                    // con := con e
                    return lhs.nonTrivialCase()?.let {rewrapToContext(it) { e -> Application(e, rhs)} }
                }
                else -> return null // trivial in other cases
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

        // ANTI_DRIVING
        /**
         * This function extracts program from process graph
         * "Inverse driving function"
         * (this is operator C' in article)
         *
         * dict maps ancestor node [alpha || this] to generated Let.body expression
         */
        fun extractProgram(dict : Map<Node, Expr>) : Expr {
            // separately process nodes with artificial let substitution
            if (letSubstitution != null) {
                return children.first().extractProgram(dict).applySub(letSubstitution)
            }

            // here we process nontrivial nodes... the heart of finite control flow representation
            if (nontrivial) {
                // rule C7.2 and C8.2 of the article
                if (backedgeParent != null) {
                    val fsig = dict[backedgeParent] ?: error("Insufficient map")
                    val gen = generalize(fsig, expression)
                    assert (gen.expr isomorphic fsig) // check just in case
                    return fsig.applySub(gen.subRight)
                }

                // rule C7.1 and C8.1 of the article
                val bb = backedged
                if (bb.size > 0) {
                    // someone in subtree needs generalization :)
                    val thetas = bb.map {
                        val gen = generalize (expr, it.expr)
                        assert(gen.expr isomorphic expr) // check just in case
                        gen.subRight // converts our expression to one of the backedged by us
                    }
                    val vi_dom = thetas.flatMap { it.keys } // get all possible substitution domains and merge them
                    val vi_new = vi_dom.map { nameGen.next() } // generate the same amount of new variables
                    val theta_dash = vi_dom.zip(vi_new).toMap().mapValues { (_, v) -> Var(v) } // then create uniform renaming and fix arity

                    val f_new = nameGen.next() // also generate fresh name for function
                    // now we have sufficient description that this node is a 'letrec' node

                    val in_expr = vi_new.fold(Function(f_new) as Expr) { e, n -> e app Var (n) }
                    val extra_dict = dict + (this to in_expr)

                    if (nontrivial_func) {
                        val child = children.firstOrNull() ?: error("No children for function node, was it even unfolded when driving?")
                        val in_generated = child.extractProgram(extra_dict).applySub(theta_dash)
                        val in_abstr = in_generated abs vi_new
                        return Let(f_new, in_abstr, in_expr)
                    } else if (nontrivial_case) {
                        val match = children.firstOrNull()?.extractProgram(extra_dict)
                            ?: error("No children for function node, was it even unfolded when driving?")

                        // Warning: if the node is nontrivial case, childrenPat != null if node was driven
                        val branches = childrenPat!!.zip(children.drop(1).map { it.extractProgram(extra_dict) })
                        val in_generated = Case(match, branches).applySub(theta_dash)
                        val in_abstr = in_generated abs vi_new
                        return Let(f_new, in_abstr, in_expr)
                    } else {
                        error ("Absurd -- the node has beeing backedged, but neither nontrivial func nor nontrivial case")
                    }

                }

                // rule C7.3 and C8.3 of the article
                if (nontrivial_func) {
                    return children.firstOrNull()?.extractProgram(dict)
                        ?: error("No children for function node, was it even unfolded when driving?")
                } else if (nontrivial_case) {
                    val match = children.firstOrNull()?.extractProgram(dict)
                        ?: error("No children for function node, was it even unfolded when driving?")

                    // Warning: if the node is nontrivial case, childrenPat != null if node was driven
                    val branches = childrenPat!!.zip(children.drop(1).map { it.extractProgram(dict) })
                    return Case(match, branches)
                } else {
                    error("Absurd -- the node has beeing backedged, but neither nontrivial func nor nontrivial case")
                }
            }

            // rule C8 of the article
            if (nontrivial_case) {
                // the same as upper case, just get memoized expression
                if (backedgeParent != null) {
                    val fsig = dict[backedgeParent] ?: error("Insufficient map")
                    val gen = generalize(fsig, expression)
                    assert (gen.expr isomorphic fsig) // check just in case
                    return fsig.applySub(gen.subRight)
                }

            }

            // otherwise, process reduction in context
            // that's easy: if here is one children, and it is marked as 'transition',
            // then this child appeared as beta reduction of current node
            if (children.size == 1) {
                val child = children.first()
                if (child.transition) return child.extractProgram(dict) // transition compression happens
            }

            // observables
            val e = expression
            when (e) {
                // 1. local variable
                is Var -> return e // straightforward
                // 2. or multiple applications to local variable:
                is Application -> {
                    // if variable is in head position, then fold variable with applications
                    if (expr.asVariableApplications() != null) {
                        return children.drop(1).fold(children.first().extractProgram(dict)) { l, r -> l app r.extractProgram(dict)}
                    }
                }
                // 3. or constructor
                is Constructor -> return Constructor(e.name, children.map { it.extractProgram(dict) })
                // 4. or lambda abstraction
                is Lambda -> return Lambda(e.name, children.first().extractProgram(dict))
            }

            error("Program extraction exhausted...")
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
                old.removeSubtreeFromUnprocessed()
                return true
            }
            for (n in children) {
                if (n.replace(old, nodeBuilder)) {
                    return true
                }
            }
            return false
        }

        private fun removeSubtreeFromUnprocessed() = (children + this).map { unprocessed.remove(it) }

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
            val processing = unprocessed.firstOrNull() ?: return i // end function when no processing nodes left
            unprocessed.remove(processing)
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

    /**
     * This function extracts program from process graph
     * "Inverse driving function"
     * (this is operator C in article)
     */
    private fun extractProgram() = root.extractProgram(mapOf())

}