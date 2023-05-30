package sls

import org.ksmt.KContext
import org.ksmt.expr.KExpr
import org.ksmt.expr.rewrite.simplify.KBoolExprSimplifier
import org.ksmt.solver.KSolverStatus
import org.ksmt.solver.z3.KZ3SMTLibParser
import org.ksmt.sort.KBoolSort
import sls.solver.SLSLover
import java.io.File
import java.lang.AssertionError
import kotlin.system.exitProcess
import kotlin.system.measureTimeMillis

fun main() {
    val n = 100
    var totalTime: Long = 0

    val sudokuFile = File("C:\\Users\\Marat\\Desktop\\smt\\sudoku9x9_0_exp.smt2")
    for (i in 0 until n) {
//        totalTime += testSingleFile(sudokuFile)
        var path: String
        path = """benchmarks\sudoku\mt_top1465"""
        path = """benchmarks\sudoku\17_clue"""
        path = """benchmarks\sudoku\hardest_1106"""
        path = """benchmarks\sudoku\kaggle"""
        path = """benchmarks\graph_coloring\SGB"""
        path = """benchmarks\bench_ab\acceptables"""
        path = """benchmarks\sage\app1\acceptables"""
        totalTime = testNFiles(File(path))
    }

    println("It took $totalTime ms")
    println("It took ${totalTime * 1.0 / n} ms average")
}

private fun testSingleFile(file: File): Long {
    val ctx = KContext()
    with(ctx) {
        // parse file
        val assertions: List<KExpr<KBoolSort>> =
            KZ3SMTLibParser(ctx).parse(file.readText().trimIndent())

        // elapsed time variable
        val timeInMillis: Long

        SLSLover(this).use { solver -> // create s SLS Smt solver instance
            // assert constraints
            for (constraint in assertions)
                solver.assert(constraint)

            // check assertions satisfiability and measure
            val satisfiability: KSolverStatus
            timeInMillis = measureTimeMillis {
                satisfiability = solver.check()
            }
            assert(satisfiability == KSolverStatus.SAT)
        }

        return timeInMillis
    }
}

private fun testNFiles(dir: File, n: Int? = null): Long {
    var totalTime: Long = 0
    if (n == null) {
        dir.walkTopDown()
            .drop(1).forEach {
                totalTime += testSingleFile(it)
            }
    } else {
        dir.walkTopDown()
            .drop(1).take(n).forEach {
                totalTime += testSingleFile(it)
            }
    }
    return totalTime
}

private fun printAssertions(assertions: List<KExpr<KBoolSort>>) {
    for (constraint in assertions)
        println(constraint.toString())
}
