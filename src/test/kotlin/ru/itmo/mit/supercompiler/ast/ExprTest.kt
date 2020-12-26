package ru.itmo.mit.supercompiler.ast

import org.testng.Assert.*
import org.testng.annotations.Test
import ru.itmo.mit.supercompiler.ast.Expressions.K
import ru.itmo.mit.supercompiler.ast.Expressions.K2
import ru.itmo.mit.supercompiler.ast.Expressions.church
import ru.itmo.mit.supercompiler.ast.Expressions.churchSuc
import ru.itmo.mit.supercompiler.ast.Expressions.churchZ
import ru.itmo.mit.supercompiler.ast.Expressions.id
import ru.itmo.mit.supercompiler.ast.Expressions.listFrom
import ru.itmo.mit.supercompiler.ast.Expressions.list_empty
import ru.itmo.mit.supercompiler.ast.Expressions.list_size
import ru.itmo.mit.supercompiler.ast.Expressions.list_xyz
import ru.itmo.mit.supercompiler.ast.Expressions.omega
import ru.itmo.mit.supercompiler.ast.Expressions.omegaBig

fun printTerm(term : String) {
    if (term.contains('\n')) {
        println("==============")
        println(term)
        println()
    } else {
        println("    $term")
    }
}

fun stepByStepPrinter(expr : Expr) {
    println("Step by step reduction of $expr")
    for (term in whnfSeq0(expr.renamedBoundVariables())) {
        printTerm("$term")
    }
}

fun stepByStepPrinter(expr : Program) {
    println("Step by step reduction of $expr")
    for (term in expr.whnfSeq()) {
        val toPrint = "$term"
        printTerm("$term")
    }
}

class ExprTest {

    @Test
    fun monitorPrettyPrinting() {
        println("id = $id")
        println("K = $K")
        println("K2 = $K2")
        println("omega = $omega")
        println("omegaBig = $omegaBig")
        println("churchZ = $churchZ")
        println("5 = ${church(5)}")
        println("suc (2)  =  ${churchSuc(church(2))}")
        println("[] = $nil")
        println("list_xyz = $list_xyz")
        println(omega.cons(id).cons(Var("haha")).cons(Var("x").app(Var("y"))).cons(omegaBig))
        println("list_empty = $list_empty")
        println("list_size = $list_size")

    }

    // isomorphic testing
    @Test
    fun isomorphicTest_K_is_not_churchZ() {
        assertFalse(K.isomorphic(churchZ))
    }
    @Test
    fun isomorphicTest_K2_is_churchZ() {
        assertTrue(K2.isomorphic(churchZ))
    }
    @Test
    fun isomorphicTest_K2repeatedArg_is_K2() {
        assertTrue(Lambda("t", Lambda("t", Var("t"))).isomorphic(K2))
    }

    @Test
    fun reductionTest_null1() {
        assertNull(whnfBetaReduction0(id))
    }
    @Test
    fun reductionTest_null2() {
        assertNull(whnfBetaReduction0(K))
    }
    @Test
    fun reductionTest_null3() {
        assertNull(whnfBetaReduction0(church(7)))
    }
    @Test
    fun reductionTest_suc2_is_WHNF() {
        assertNull(whnfBetaReduction0(churchSuc(church(2))))
    }

    @Test
    fun reductionTest_omegaToOmega() {
        assertTrue(whnfBetaReduction0(omegaBig)!!.isomorphic(omegaBig))
    }
    @Test
    fun whnfTest_suc2xy_is_3xy() {
        val x = Var("p")
        val y = Var("q")

        val suc2xy = churchSuc(church(2)).app(x).app(y).renamedBoundVariables()
        val suc2xy_nf = whnf0(suc2xy)
        stepByStepPrinter(suc2xy)
        println("$suc2xy ->* $suc2xy_nf")

        val c3xy = church(3).app(x).app(y).renamedBoundVariables()
        val c3xy_nf = whnf0(c3xy)
        stepByStepPrinter(c3xy)
        println("$c3xy ->* $c3xy_nf")

        // equals because they have the same variables
        assertTrue(suc2xy_nf.equals(c3xy_nf))
    }

    @Test
    fun patternMatching_list_xyz_empty() {
        stepByStepPrinter(list_empty.app(list_xyz))
        val res = whnf0(list_empty.app(list_xyz).renamedBoundVariables())
        assertTrue(res.isomorphic(churchZ))
    }

    @Test
    fun patternMatching_list_xyz_length() {
        stepByStepPrinter(list_size.fmap { app(list_xyz) })
        // to break WHNF add some globals
        var u = Var("u")
        var v = Var("v")
        val res = list_size.fmap { app(list_xyz).app(u).app(v) }.whnf().toExpr()
        assertTrue(res.isomorphic(church(3).app(u).app(v)))
    }
}