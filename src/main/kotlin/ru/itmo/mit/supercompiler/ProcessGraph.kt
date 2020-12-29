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

    private val nodeNameGenerator = Generator.numberedVariables("node").iterator()

    // initialize set of unprocessed nodes
    private val unprocessed : MutableSet<Node> = mutableSetOf()
    // initialize with target expression and global functions context 'where'
    private var root : Node = Node(program.expression, null)
    private var where : Where = program.where
    // and even initialize proper names generator, so no collisions occur
    private val nameGen = Generator.numberedVariables("s",
        program.expression.boundVars + program.expression.freeVars + where.keys).iterator()


    init {
        try {
            // after that, initialization continues with building process tree (potentially infinite process)
            buildProcessTree()
            // now the class is ready for program extraction
        } finally {
            println()
            println("+=============+")
            println("| Final Graph |")
            println("+=============+")
            println()
            println(dump())
            println()
        }
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
                             val transition : Boolean = false,
                             ) {
        val name = nodeNameGenerator.next() // name node for dump purpose
        init {
            // place yourself in unprocessed list :)
            unprocessed.add(this)
        }

        var expr get() = expression // expose read only property
                 set(it) { expression = if (expr.isValid()) it else expr.renameWithContext(nameGen) }
        val backedge get() = backedgeParent
        // also provide collection of nodes backedged by current node
        val backedged : List<Node> get() = getBackedged(this)

        fun getBackedged(to: Node) : List<Node> {
            val res = children.flatMap { it.getBackedged(to) }
            if (backedgeParent == to) {
                return res + this
            }
            return res
        }

        // other Node properties
        val processed get() = backedgeParent != null // variable is processed if it has backedge
                || (expr.let{it is Constructor && it.args.isEmpty()}) // or if it is zero arity constructor
                || expr is Var // or it is LOCAL (?) variable (guess just Var, not Fun)

        val nontrivial_func = expr.isNontrivial().first
        val nontrivial_case = expr.isNontrivial().second
        val nontrivial = expr.isNontrivial().let { it.first || it.second }
        val trivial = !nontrivial && !processed

        tailrec fun Expr.isNontrivial() : Pair<Boolean, Boolean> {
            when (this) {
                is Var -> return false to true
                is Function -> return true to false
                is Case -> {
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
            expr =  f (expr)
            return this
        }

        /// DRIVING
        /**
         * The function performs driving ands saves result to the children variable
         */
        fun drive() {
            if (!children.isEmpty()) error("The node have been driven twice!")
            println("Driving expr: $expr")
            children.addAll(expr.driveRec())
            println("Got children: ${children.map{it.expr}}")
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
                val letExpr = expr
                expr = letSubstitution.entries.fold(letExpr) {e, (n, d) -> Let(n, d, e)}
                return listOf(Node(letExpr, this@Node)) + letSubstitution.values.map { Node(it, this@Node) }
            }
            // observables
            when (this) {
                is Let -> error ("Whoa, cannot process Let expression because I consider target expression from Program")
                // 1. local variable
                // 2. or multiple applications to local variable:
                is Application -> {
                    // look up for head
                    val (head, varApp) = asApplicationList()
                    // if it is variable in head position, fold arguments to the list
                    if (head is Var) {
                        varApp.map { e -> Node(e, this@Node)}
                    }
                }
                // 3. or constructor
                is Constructor -> return args.map {Node(it, this@Node)}
                // 4. or lambda abstraction
                is Lambda -> return listOf(Node(body, this@Node))
            }
            // otherwise, process reduction in context
            val reducedByBeta = driveBetaReduction()
            reducedByBeta?.let { return listOf(it) }
            // otherwise, process nontrivial case
            nonTrivialCase()?.let { (head, branches) ->
                childrenPat = branches.map { (p, _) -> p} // we make this nontrivial case node, so remember patterns
                val children = listOf(head) + branches.map { (_, e) -> Node(e, this@Node) } // return all collected nodes + head node
                return children
            }
            // error("Driving exhausted. Maybe the term is invalid?")
            // maybe this term is stuck actually :)
//            println("WARNING: Found stuck term: $expr")
            return(listOf())
        }

        /**
         * driving with context reductions -- reminds beta reduction
         * this reductions are usually transition compressed before yielding the final program
         * @see ru.itmo.mit.supercompiler.Program.whnfBetaReduction
         */
        private fun Expr.driveBetaReduction() : Node? {
            when (this) {
                is Function -> return where[name]?.let {Node( it , this@Node, transition = true)}
                is Application -> {
                    if (lhs is Lambda) {
                        // con<(\v -> body) @ rhs>   =>   con< body {v := rhs} >
                        return lhs.body.substituteVar(Var(lhs.name), rhs).let { Node(it, this@Node, transition = true) }
                    } else {
                        // maybe redex in lhs according to 'con := con e' rule
                        return lhs.driveBetaReduction()?.let { it.fmapExpr { Application(it.expr, rhs) } }
                    }
                }
                is Case -> {
                    // 'con := case con of ...
                    match.driveBetaReduction()?.let { return it.fmapExpr { Case(it.expr, branches) } }
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
                    val (head, varApp) = match.asApplicationList()
                    if (head is Var || head is Function && head.builtin) {

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
                return children.first().extractProgram(dict)
                    .applySub(letSubstitution.keys.zip(children.drop(1).map {it.expr}).toMap())
            }

            // here we process nontrivial nodes... the heart of finite control flow representation
            if (nontrivial) {
                // rule C7.2 and C8.2 of the article
                if (backedgeParent != null) {
                    val fsig = dict[backedgeParent]
                        ?: error("Insufficient map")
                    val gen = generalize(fsig, expr)
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
                    val fsig = dict[backedgeParent]
                            ?: error("Insufficient map")
                    val gen = generalize(fsig, expr)
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
            val e = expr
            when (e) {
                // 1. local variable
                is Var -> return e // straightforward
                // 2. or multiple applications to local variable:
                is Application -> {
                    // if variable is in head position, then fold variable with applications
                    val (head, _) = expr.asApplicationList()
                    if (head is Var || head is Function && head.builtin) {
                        return children.drop(1).fold(children.first().extractProgram(dict)) { l, r -> l app r.extractProgram(dict)}
                    }
                }
                // 3. or constructor
                is Constructor -> return Constructor(e.name, children.map { it.extractProgram(dict) })
                // 4. or lambda abstraction
                is Lambda -> return Lambda(e.name, children.first().extractProgram(dict))
            }

            // error("Program extraction exhausted...")
            // maybe this term is stuck actually :)
//            print("WARNING [extraction]: Found stuck term: $expr")
            return(expr)
        }

        /**
         * This function replaces node n with expression e
         *
         * the nodeBuilder takes parent node as an argument
         */
        fun replace(old : Node, nodeBuilder : (Node?) -> Node) : Node? {
            if (old == this) {
                if (parent == null) error("Parent should be not null")
                // uhh, ugly
                val id = parent.children.indexOf(old)
                parent.children.removeAt(id)
                parent.children.add(id, nodeBuilder(parent))
                old.removeSubtreeFromUnprocessed()
                return old
            }
            for (n in children) {
                n.replace(old, nodeBuilder)?.let { return it }
            }
            return null
        }

        /**
         * Returns first ancestor that satisfies bi-argument predicate
         * The first argument is expression from uppermost node, the second argument is from bottommost node
         */
        fun ancestor(predicate : (Node, Node) -> Boolean) : Node? {
            var res = parent
            while (res != null) {
                if (predicate(res, this)) return res
                res = res.parent
            }
            return null
        }

        // folds e2 expression to the receiver
        infix fun fold(e2 : Node) {
            e2.backedgeParent = this
        }

        /**
         * Dumps subtree
         */
        fun dump(sb : StringBuilder) : StringBuilder {
            sb.appendLine("{")
            sb.appendLine("\"name\": \"$name\",")
            sb.appendLine("\"expr\": \"${expr.toString().replace('\n', ' ')}\",")
            sb.appendLine("\"trivial\": \"$trivial\",")
            sb.appendLine("\"transition\": \"$transition\",")
            sb.appendLine("\"children\": [${children.map { it.name }.joinToString ("\", \"", "\"", "\"" )}],")
            sb.appendLine("\"parent\": \"${parent?.name}\",")
            sb.appendLine("\"backedge\": \"${backedge?.name}\"")
            sb.appendLine("},")
            children.map {it.dump(sb)}
            return sb
        }

    }

    /**
     * Replaces node 'n' in the tree (by ref) with fresh node with expression e
     */
    private fun replace(old : Node, nodeBuilder : (Node?) -> Node) : Node? {
        if (old == root) {
            root = nodeBuilder(null)
            old.removeSubtreeFromUnprocessed()
            return old
        }
        return root.replace(old, nodeBuilder)
    }
    private fun Node.removeSubtreeFromUnprocessed() : Unit
    {
        unprocessed.remove(this);
        children.forEach() {  it.removeSubtreeFromUnprocessed() }
    }

    /**
     * Performs abstraction of node 'alpha' with respect to node 'beta'
     */
    private fun abstract(alpha : Node, beta : Node) : Node? {
        val generalization = generalize(alpha.expr, beta.expr)
        val old = replace(alpha) { p -> Node(generalization.expr, p, generalization.subLeft) }
        return old
    }

    private fun isRenaming(substitution: Substitution) = substitution.values.all { it is Var }

    /**
     * The most important function: builds process tree of the program
     * Returns amount of steps just for curiosity
     */
    private fun buildProcessTree() : Int {
        fun ddump(x : Int) {
            println()
            println("=================")
            println("Step #$x")
            println("=================")
            println(dump())
            println("=================")
            println()
        }
        var i = 0
        while (true) {
            val processing = unprocessed.firstOrNull() ?: return i // end function when no processing nodes left
            unprocessed.remove(processing)
            i++
            if (i > 200) {
                error("Stop iteration")
            }

            println("")
            println("=================")
            print("Step #$i [${processing.name}] <- [${processing.parent?.name}]")

            if (processing.trivial) {
                println("  [Trivial]")

                processing.drive()
                continue
            }

            val renamingAncestor = processing.ancestor { ancestor, proc ->
                val generalization = generalize(ancestor.expr, proc.expr)
                isRenaming(generalization.subLeft) && isRenaming(generalization.subRight)
//                        && !ancestor.transition
            }
            if (renamingAncestor != null) {
                println("  [Folding]")
                println("    node     #${processing.name} => ${processing.expr}")
                println("    renaming #${renamingAncestor.name} => ${renamingAncestor.expr}")
                renamingAncestor.fold(processing)
                continue
            }

            val substAncestor = processing.ancestor{ ancestor, proc ->
                val generalization = generalize(ancestor.expr, proc.expr)
                isRenaming(generalization.subLeft)
                        && !ancestor.transition
            }
            if (substAncestor != null) {
                println("  [Substitution]")

                println("    node     #${processing.name} => ${processing.expr}")
                println("    similar  #${substAncestor.name} => ${substAncestor.expr}")
                val old = abstract(processing, substAncestor)
                println("    replaced #${old?.name}")
                continue
            }

            val whistleAncestor = processing.ancestor {ancestor, proc ->
                ancestor.expr homoCoupling proc.expr
                    && !ancestor.transition && ancestor.parent?.letSubstitution == null
            }
            if (whistleAncestor != null) {

                println("  [Coupling]")
                println("    node     #${processing.name} => ${processing.expr}")
                println("    similar  #${whistleAncestor.name} => ${whistleAncestor.expr}")
                println("    generalization => ${generalize(whistleAncestor.expr, processing.expr).expr}")
//                println("  Graph:")
//                println(dump())
                val old = abstract(whistleAncestor, processing)
                println("    replaced #${old?.name}")

                println("  New graph:")
                println(dump())
                println("  [End Coupling]")
                continue
            }

            println("  [Driving]")
            processing.drive()
        }
    }

    /**
     * This function extracts program from process graph
     * "Inverse driving function"
     * (this is operator C in article)
     */
    private fun extractProgram() = root.extractProgram(mapOf())


    /**
     * Dumps graph
     */
    fun dump() : String {
        val sb = StringBuilder()
        sb.appendLine("[")
        root.dump(sb)
        sb.appendLine("]")
        return sb.toString()
    }
}