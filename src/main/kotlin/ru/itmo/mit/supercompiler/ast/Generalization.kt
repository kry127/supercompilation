@file:Suppress("NonAsciiCharacters")

package ru.itmo.mit.supercompiler.ast

typealias Substitution = Map<String, Expr>

/**
 * Generalization
 */
class Generalization private constructor(val expr : Expr, val subLeft : Substitution, val subRight : Substitution) {

    fun fmap(f : (Expr) -> Expr) : Generalization {
        return Generalization(f (expr), subLeft, subRight)
    }

    companion object {
        /**
         * We assume that keys are not intersecting, so we use simple substitution merge rule
         */
        private fun List<Substitution>.flatten() : Substitution = this.flatMap { it.entries }.associate { (k, v) -> k to v }

        private fun Iterator<String>.trivialGeneralization(e1: Expr, e2: Expr) : Generalization {
            // check if expressions are equal and return empty generalization
            if (e1.equals(e2)) {
                return Generalization(e1, mapOf(), mapOf())
            }
            // TODO think about e1.isomorphic(e2) -- this is a RENAMING
            val newVarName = next()
            return Generalization(Var(newVarName), mapOf(newVarName to e1), mapOf(newVarName to e2))
        }

        private fun List<Generalization>.flatten(exprFactory : (List<Expr>) -> Expr) : Generalization {
            val expr = exprFactory(map{it.expr})
            val subLeft  = map{it.subLeft} .flatten()
            val subRight = map{it.subRight}.flatten()
            return Generalization(expr, subLeft, subRight)
        }

        infix fun Expr.П(other: Expr) = generalize(this, other)
        fun generalize(lhs: Expr, rhs: Expr) : Generalization {
            // TODO do we really can't do this?
            if (!lhs.isValid() && !rhs.isValid()) error("cannot generalize expressions with collisions")

            // use the same generator to avoid generated variables name collision
            val gen = Generator.numberedVariables("c",
                lhs.freeVars union lhs.boundVars union rhs.freeVars union rhs.boundVars).iterator()

            // all renaming should happen in context of the single name generator for correctness
            val wastefulGeneralization =  gen.generatorGeneralizer(lhs, rhs)

            // when first part of algo is completed, clean up variables named differently which maps to the same content
            return refine(wastefulGeneralization)
        }

        private fun Iterator<String>.generatorGeneralizer(e1 : Expr, e2 : Expr) : Generalization {
            if (e1 is Constructor && e2 is Constructor && e1.name == e2.name && e1.args.size == e2.args.size) {
                val generalizationResults = e1.args.zip(e2.args).map {(l, r) -> generatorGeneralizer(l, r) }
                return generalizationResults.flatten { Constructor(e1.name, it) }
            }
            if (e1 is Lambda && e2 is Lambda) {
                val (newCommonName, rawGeneralization) =  boundVarGeneralize(e1.body, e2.body, e1.name, e2.name)
                return rawGeneralization.fmap { Lambda(newCommonName, it) } // abstract by common name
            }
            if (e1 is Application && e2 is Application) {
                val lhsGen = generatorGeneralizer(e1.lhs, e2.lhs)
                val rhsGen = generatorGeneralizer(e1.rhs, e2.rhs)
                return listOf(lhsGen, rhsGen).flatten { (l, r) -> l.app(r) }
            }
            // Note: we compute case with top-down strategy, so we don't consider permutation of branches
            if (e1 is Case && e2 is Case
                && e1.branches.zip(e2.branches).all { (p1, p2) -> p1.first match p2.first }) {
                // if conditions are met, generalize
                val matchGen = generatorGeneralizer(e1.match, e2.match)
                // generalize each branch, you'll get a pair of:
                //  1. pattern with fresh variables
                //  2. generalization of branches from the two cases
                val (freshPatterns, generalizations) = e1.branches.zip(e2.branches)
                    .map { (bl, br) ->
                        val (patternLeft, exprLeft) = bl
                        val (patternRight, exprRight) = br
                        val (newCommonNames, rawGeneralization) = boundVarsGeneralize(exprLeft, exprRight,
                            patternLeft.args.map {it.name}, patternRight.args.map {it.name})
                        // make the same pattern (both names are equal, and arity of vector)
                        // BUT, variable names are fresh, and the body is generalized :)
                        Pattern(patternLeft.name, newCommonNames.map {Var(it)}) to rawGeneralization
                    }.unzip()
                // make combined case expression of generalizations
                return (generalizations + matchGen).flatten { newExprs ->
                    val newMatch = newExprs.last()
                    val newBranches = freshPatterns.zip(newExprs)
                    Case(newMatch, newBranches)
                }
            }
            // no help from other branches, generate the most vague generalization
            return trivialGeneralization(e1, e2)
        }

        /*
         * this function is used to generalize e1 and e2 w.r.t. bound variable bvl, bvr
         *  1. we make bvl == bvr by renaming: generate fresh newName variable
         *  2. make substitution in left and right expressions: { bvl -> new }, {bvr -> new} respectively
         *  3. now if they properly structurally generalize (with equal same bound var) we can
         *     safely abstract them by variable newName
         *
         *  Returns: new common name and generalization of both expressions
         */
        private fun Iterator<String>.boundVarGeneralize(lhs : Expr, rhs : Expr, bvl : String, bvr : String) : Pair<String, Generalization> {
            val newName = this.next()
            val (v1, v2, vn) = listOf(bvl, bvr, newName).map{Var(it)}
            val newExpr1 = lhs.substituteVar(v1, vn)
            val newExpr2 = rhs.substituteVar(v2, vn)
            // we can use abstraction by newName, because domains of substitution are not collide
            // with new bound variable => final substitution to the new lambda is legit
            return newName to generatorGeneralizer(newExpr1, newExpr2)
        }


        /**
         * Version of boundVarGeneralize in multiple form. Just see upper comments
         */
        private fun Iterator<String>.boundVarsGeneralize(lhs : Expr, rhs : Expr, bvl : List<String>, bvr : List<String>) : Pair<List<String>, Generalization> {
            val n = bvl.size
            if (bvr.size != n) error("Incompatible list size")

            val newNames = (1..n).map { next () }
            val newExpr1 = bvl.zip(newNames).fold(lhs) { l, (v1, vn) -> l.substituteVar(Var(v1), Var(vn))}
            val newExpr2 = bvr.zip(newNames).fold(rhs) { r, (v2, vn) -> r.substituteVar(Var(v2), Var(vn))}
            return newNames to generatorGeneralizer(newExpr1, newExpr2)

        }

        /**
         * Common subexpression filtering
         * This is last optimization applied to maps -- it assigns the same name to variables, which
         * substitute the same expression
         */
        private fun refine(generalization: Generalization) : Generalization {
            val eqSet = congruentVariables(generalization.subLeft, generalization.subRight)
            // then for each group of variables we should make join
            var ex = generalization.expr
            val subLeft = generalization.subLeft.toMutableMap()
            val subRight = generalization.subRight.toMutableMap()
            for (set in eqSet) {
                if (set.size == 1) continue // no need to join single variable
                // everyone in set should be replaced with one single representator
                val representative = set.first()
                for (other in set - representative) {
                    ex = ex.substituteVar(Var(other), Var(representative))
                    subLeft -= other
                    subRight -= other
                }
            }
            return Generalization(ex, subLeft.toMap(), subRight.toMap())
        }

        private fun <T> nullableIntersect(l : List<T>?, r : List<T>?) : Set<T>{
            if (r == null) {
                return l?.toSet() ?: setOf()
            } else {
                return l?.intersect(r) ?: r.toSet()
            }
        }

        /**
         * This function returns groups of congruent variables.
         * This is such variables, that have the same name and they map to the same expression
         */
        private fun congruentVariables(left : Substitution, right : Substitution) : List<Set<String>> {
            // we use renamed form of expressions so equals() can properly work
            // but! these are the "keys"! Do not use this modified expressions at target
            val flipL = left .entries.groupBy ({ (_, e) -> e.renamedBoundVariables() }) { (l, _) -> l}
            val flipR = right.entries.groupBy ({ (_, e) -> e.renamedBoundVariables() }) { (l, _) -> l}

            // that's how we get variables that should have the same name:
            return (flipL.keys + flipR.keys).map { nullableIntersect(flipL[it], flipR[it]) }
        }
    }
}