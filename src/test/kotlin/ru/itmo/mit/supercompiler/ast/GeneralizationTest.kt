package ru.itmo.mit.supercompiler.ast

import org.testng.Assert.assertTrue
import org.testng.annotations.Test
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.cons
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.nil

class GeneralizationTest {

    fun generalizationPrinter(expr1: Expr, expr2: Expr) {
        val generalization = Generalization.generalize(expr1, expr2)
        println("$expr1 П $expr2 = ${generalization.expr}")
        println("subst 1 = ${generalization.subLeft}")
        println("subst 2 = ${generalization.subRight}")
    }

    // a couple of instances showed in article
    @Test
    fun instance1() {
        val expr1 = Function("map") app (Function("f"))
        val expr2 = Function("map") app (Function("compose") app Function("f") app Function("g"))
        generalizationPrinter(expr1, expr2)
    }

    @Test
    fun instance2() {
        val expr1 = nil abs "x"
        val expr2 = Var("a") cons nil abs "x"
        generalizationPrinter(expr1, expr2)
    }

    @Test
    fun instance3() {
        // this generates incorrect substitution, so this
        // property should not evaluate: expr1 ◁ expr2
        val expr1 = nil abs "x"
        val expr2 = Var("x") cons nil abs "x"
        generalizationPrinter(expr1, expr2)
    }

    @Test
    fun instance4() {
        val expr1 = makeArticleCases(Function("f"), Var("b"))
        val expr2 = makeArticleCases(Function("g"), Var("b"))
        generalizationPrinter(expr1, expr2)
    }

    @Test
    fun instance5() {
        val expr1 = makeArticleCases(Function("f"), Var("b"))
        val expr2 = makeArticleCases(Function("f") app Function("g"), Var("b"))
        generalizationPrinter(expr1, expr2)
    }

    @Test
    fun instance6() {
        val expr1 = makeArticleCases(Function("f"), Var("b"))
        val expr2 = makeArticleCases(Function("f"), Function("g") app Var("b"))
        generalizationPrinter(expr1, expr2)
    }

    // random tests
    fun checkThatExprsIsARenamingOfGeneralization(expr1: Expr, expr2: Expr, silent : Boolean = false) {
        val generalization = Generalization.generalize(expr1, expr2)
        val expr1_restore = generalization.expr.applySub(generalization.subLeft)
        val expr2_restore = generalization.expr.applySub(generalization.subRight)
        if (!silent) {
            println("Common expr: ${generalization.expr}")
            println("Subst1: ${generalization.subLeft}")
            println("Subst1: ${generalization.subRight}")
            println()
            println("$expr1_restore ==? $expr1")
            println()
        }
        assertTrue(expr1_restore isomorphic expr1)
        if (!silent) {
            println("$expr2_restore ==? $expr2")
            println()
        }
        assertTrue(expr2_restore isomorphic expr2)
    }
    @Test
    fun randomTest_checkThatExprsIsARenamingOfGeneralization_verbose() {
        val varNames = setOf("x", "y", "z")
        val funNames = setOf("f", "g", "h")
        val ktorNames = setOf("True", "False")
        val treeGen = RandomExprGenerator(varNames,funNames, ktorNames, 5, 3, 134723)

        repeat(1000) {
            println()
            println(" === #$it ===")

            checkThatExprsIsARenamingOfGeneralization(treeGen.next().renamedBoundVariables(),
                                                      treeGen.next().renamedBoundVariables())
        }
    }

    @Test
    fun randomTest_checkThatExprsIsARenamingOfGeneralization_silent1() {
        val varNames = setOf("x", "y", "z")
        val funNames = setOf("f", "g", "h")
        val ktorNames = setOf("True", "False")
        val treeGen = RandomExprGenerator(varNames,funNames, ktorNames, 7, 3, 349133)

        repeat(10000) {
            checkThatExprsIsARenamingOfGeneralization(treeGen.next().renamedBoundVariables(),
                treeGen.next().renamedBoundVariables(), silent = true)
        }
    }

    @Test
    fun randomTest_checkThatExprsIsARenamingOfGeneralization_deep() {
        val varNames = setOf("x", "y", "z")
        val funNames = setOf("f", "g", "h")
        val ktorNames = setOf("True", "False")
        val treeGen = RandomExprGenerator(varNames,funNames, ktorNames, 22, 5, 144209)

        repeat(1000) {
            checkThatExprsIsARenamingOfGeneralization(treeGen.next().renamedBoundVariables(),
                treeGen.next().renamedBoundVariables(), silent = true)
        }
    }
}