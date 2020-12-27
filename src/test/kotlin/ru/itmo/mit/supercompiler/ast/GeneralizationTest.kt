package ru.itmo.mit.supercompiler.ast

import org.testng.Assert.*
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

    // this is a test for homeomorphic inception
    fun makeCustomCases(a : Expr, b : Expr) = makeCase(Var("x"), makePattern("Z") to Var("x"),
        makePattern("S", "b") to (a app b))

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
        val expr1 = makeCustomCases(Function("f"), Var("b"))
        val expr2 = makeCustomCases(Function("g"), Var("b"))
        generalizationPrinter(expr1, expr2)
    }

    @Test
    fun instance5() {
        val expr1 = makeCustomCases(Function("f"), Var("b"))
        val expr2 = makeCustomCases(Function("f") app Function("g"), Var("b"))
        generalizationPrinter(expr1, expr2)
    }

    @Test
    fun instance6() {
        val expr1 = makeCustomCases(Function("f"), Var("b"))
        val expr2 = makeCustomCases(Function("f"), Function("g") app Var("b"))
        generalizationPrinter(expr1, expr2)
    }
}