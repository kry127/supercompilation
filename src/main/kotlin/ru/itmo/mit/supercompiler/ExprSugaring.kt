package ru.itmo.mit.supercompiler

import ru.itmo.mit.supercompiler.Generator.numberedVariables

/**
 * Блок 'where' -- это просто отображение из глобального имени в выражение
 */
typealias Where = Map<String, Expr>

fun Expr.toProgram(globals : Map<String, Expr> = mapOf()) = Program.convertToProgram(this, globals)

// some lambda calculus
infix fun Expr.app(other: Expr) : Expr = Application(this, other)
infix fun Expr.abs(name : String) : Lambda = Lambda(name, this)
infix fun Expr.abs(names : List<String>) = names.reversed().fold(this) { e, n -> e abs n }

// pattern matching sugar
fun makePattern(name : String, vararg x : String) = Pattern(name, x.map { Var(it) })
fun Constructor.toPattern(): Pair<Pattern, List<String>> {
    val generatedNames = numberedVariables("p").take(args.size).toList()
    val pattern = Pattern(name, generatedNames.map { Var(it) })
    return Pair(pattern, generatedNames)
}
fun makeCase(match : Expr, vararg fill : Pair<Pattern, Expr>) : Case {
    return Case(match, fill.map {(x, y) -> Pair(x, y)})
}

// supercompilation sugar
fun supercompile(program: Program) : Program {
    return ProcessGraph.supercompile(program)
}