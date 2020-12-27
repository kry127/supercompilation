package ru.itmo.mit.supercompiler.ast

import ru.itmo.mit.supercompiler.ast.Constructor.Companion.cons
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.nil
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.num
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.zero
import kotlin.random.Random
import kotlin.random.nextInt

class RandomExprGenerator(val varNames: Set<String>, val funNames: Set<String>, val ktorNames : Set<String>,
                          val maxHeight: Int, val maxWidth: Int, seed: Long? = null) : Iterator<Expr> {

    val rnd = Random(seed ?: System.currentTimeMillis())

    init {
        if (maxHeight < 0) {
            error("Max available height should not be negative! You shouldn't build useless surrealistic trees.")
        }
    }
    fun randomLeaf() : Expr {
        return when (rnd.nextInt(0..3)) {
            0 -> Var(varNames.random(rnd))
            1 -> Function(funNames.random(rnd))
            2 -> nil
            else -> zero
        }
    }
    fun generateRandomList(height: Int) : Expr =
        if (height <= 0) nil
        else createRandomTree(height - 1) cons generateRandomList(rnd.nextInt(0..height - 1))

    fun generateRandomPattern() : Pattern {
        return when(rnd.nextInt(0..4)) {
            0 -> nil.toPattern().first
            1 -> makePattern("Cons", *(1..2).map{varNames.random(rnd)}.toTypedArray())
            2 -> zero.toPattern().first
            3 -> makePattern("S", varNames.random(rnd))
            else -> makePattern(ktorNames.random(rnd), *(1..maxWidth).map{varNames.random(rnd)}.toTypedArray())
        }

    }

    fun createRandomTree(height: Int) : Expr {
        if (height <= 0) return randomLeaf()

        return when (rnd.nextInt(0..6)) {
            0 -> Var(varNames.random(rnd))
            1 -> Function(funNames.random(rnd))
            2 -> nil
            3 -> generateRandomList(height)
            4 -> num(height - 1)
            5 -> Lambda(varNames.random(rnd), createRandomTree(height - 1))
            6 -> Case(createRandomTree(height - 1), (0..maxWidth).map { generateRandomPattern() to createRandomTree(height - 1) })
            else -> zero
        }

    }

    override fun hasNext() = true // always has next :D

    override fun next(): Expr = createRandomTree(rnd.nextInt(1..maxHeight))
}