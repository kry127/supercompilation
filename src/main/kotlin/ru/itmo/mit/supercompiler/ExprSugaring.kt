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

infix fun List<String>.arrow(other: Expr) = other.abs(this)

// pattern matching sugar
fun makePattern(name : String, vararg x : String) = Pattern(name, x.map { Var(it) })
fun makeCase(match : Expr, vararg fill : Pair<Pattern, Expr>) : Case {
    return Case(match, fill.map {(x, y) -> Pair(x, y)})
}

/**
 * This function collects applications to single list if there is
 * a variable in the head position. In other case it returns null
 */
fun Expr.asApplicationList() : Pair<Expr, List<Expr>> {
    return when (this) {
        is Application -> lhs.asApplicationList().let {(h, t) -> h to t + rhs }
        else -> this to listOf()
    }
}

// supercompilation sugar
fun supercompile(program: Program, debug :Boolean = false) : Program {
    return ProcessGraph.supercompile(program, debug)
}