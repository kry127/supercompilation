package ru.itmo.mit.supercompiler.ast

import org.testng.Assert.*
import org.testng.annotations.Test
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.cons
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.nil

class HomeomorphicEmbedding {
    // some instances from article
    private val a = Var("a")
    private val x = Var("x")
    private val y = Var("y")
    private val f = Function("f")
    private val g = Function("g")
    private val map = Function("map")
    private val compose = Function("compose")
    @Test
    fun instance1() {
        assertTrue(x homo y)
    }

    @Test
    fun instance2() {
        assertFalse(map homo compose)
    }

    @Test
    fun instance3() {
        assertFalse(map app f homo  (compose app f app g))
    }

    @Test
    fun instance4() {
        assertTrue(map app f homoCoupling  (map app (compose app f app g)))
    }

    @Test
    fun instance5() {
        assertTrue(nil abs x.name homoCoupling  (a cons nil).abs(x.name))
    }

    @Test
    fun instance6() {
        assertFalse(nil abs x.name homo  (x cons nil).abs(x.name))
    }

    @Test
    fun instance7() {
        val expr1 = makeArticleCases(Var("f"), Var("b"))
        val expr2 = makeArticleCases(Var("g"), Var("b"))
        assertTrue(expr1 homoCoupling  expr2)
    }

    @Test
    fun instance8() {
        val expr1 = makeArticleCases(Var("f"), Var("b"))
        val expr2 = makeArticleCases(Var("f") app Var("g"), Var("b"))
        assertFalse(expr1 homoCoupling expr2)
    }

    @Test
    fun instance9() {
        val expr1 = makeArticleCases(Var("f"), Var("b"))
        val expr2 = makeArticleCases(Var("f"), Var("g") app Var("b"))
        assertFalse(expr1 homoCoupling expr2)
    }
}