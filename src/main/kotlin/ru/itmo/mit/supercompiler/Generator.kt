package ru.itmo.mit.supercompiler

object Generator {
    /*
     * The simplest generator of bound variables
     */
    fun numberedVariables(prefix : String, isValid : (String) -> Boolean = { true }) : Sequence<String> {
        var i = 0
        return generateSequence {
            while (true) {
                if (isValid("$prefix${++i}")) break
            }
            "$prefix$i"
        }
    }

    fun numberedVariables(prefix : String, except : Set<String>) : Sequence<String> {
        return numberedVariables(prefix) {!(it in except)}
    }

}