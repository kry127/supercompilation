package ru.itmo.mit.supercompiler.ast

/**
 * Блок 'where' -- это просто отображение из глобального имени в выражение
 */
typealias Where = Map<String, Expr>

fun Expr.toProgram() = Program.convertToProgram(this)

// some lambda calculus
fun Expr.app(other: Expr) : Expr = Application(this, other)
fun Expr.abs(name : String) : Lambda = Lambda(name, this)

fun Expr.cons(other : Expr) = Constructor("Cons", listOf(this, other))
val nil = Constructor("Nil", listOf())

// pattern matching sugar
fun makePattern(name : String, vararg x : String) = Pattern(name, x.map { Var(it) })
fun makeCase(match : Expr, vararg fill : Pair<Pattern, Expr>) : Case {
    return Case(match, fill.map {(x, y) -> Pair(x, y)})
}