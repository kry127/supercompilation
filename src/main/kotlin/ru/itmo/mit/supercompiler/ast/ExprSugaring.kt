package ru.itmo.mit.supercompiler.ast

import ru.itmo.mit.supercompiler.ast.Generator.makePostfixNumberSequence

/**
 * Блок 'where' -- это просто отображение из глобального имени в выражение
 */
typealias Where = Map<String, Expr>

fun Expr.toProgram() = Program.convertToProgram(this)

// some lambda calculus
fun Expr.app(other: Expr) : Expr = Application(this, other)
fun Expr.abs(name : String) : Lambda = Lambda(name, this)

// pattern matching sugar
fun makePattern(name : String, vararg x : String) = Pattern(name, x.map { Var(it) })
fun Constructor.toPattern(): Pair<Pattern, List<String>> {
    val generatedNames = makePostfixNumberSequence("p").take(args.size).toList()
    val pattern = Pattern(name, generatedNames.map { Var(it) })
    return Pair(pattern, generatedNames)
}
fun makeCase(match : Expr, vararg fill : Pair<Pattern, Expr>) : Case {
    return Case(match, fill.map {(x, y) -> Pair(x, y)})
}