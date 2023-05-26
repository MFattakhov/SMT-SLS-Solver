package sls

import org.ksmt.KContext
import org.ksmt.solver.KSolverStatus
import org.ksmt.solver.z3.KZ3SMTLibParser
import sls.solver.SLSLover
import java.io.File
import kotlin.system.exitProcess
import kotlin.system.measureTimeMillis

fun main() {
    val ctx = KContext()
    var totalTime: Long = 0

//    File("C:\\Users\\Marat\\Desktop\\smt\\sls\\app\\src\\main\\kotlin\\sls\\bench_ab").walkTopDown().drop(1).forEach {
//        totalTime += test(ctx, it.readText())
//    }

    val sudokuFormula = File("C:\\Users\\Marat\\Desktop\\smt\\sudoku9x9_1.smt2").readText().trimIndent()
    val n = 10
    for (i in 0 until n)
        totalTime += test(ctx, sudokuFormula)
    println("It took $totalTime ms")
    println("It took ${totalTime / n} ms average")
}

private fun test(ctx: KContext, formula: String): Long =
    with(ctx) {
        // create symbolic variables
//        val a1 by boolSort
//        val a2 by boolSort
//        val a3 by boolSort
//        val b by bv32Sort
//        val d by bv32Sort
//        val e by bv32Sort

        // create expression
//        val constraint = mkBvUnsignedGreaterExpr(b, mkBv(1)) and mkBvUnsignedLessExpr(b, mkBv(5)) // 5 > b > 1
//        val constraint = mkBvMulExpr(b, mkBv(5)) eq mkBv(125) // 5 * b = 125
//        val constraint =
//            mkBvUnsignedRemExpr(b, mkBv(5)) eq mkBv(0) and
//                    mkBvUnsignedLessExpr(mkBv(100), b) // b % 5 == 0 && b > 100

        val assertions = KZ3SMTLibParser(ctx).parse(formula)
//        for (constraint in assertions)
//            println(constraint.toString())

        val timeInMillis: Long
        SLSLover(this).use { solver -> // create s SLS Smt solver instance
            // assert expressions
            for (constraint in assertions)
                solver.assert(constraint)

            // check assertions satisfiability with timeout
            timeInMillis = measureTimeMillis {
                val satisfiability = solver.check()
                assert(satisfiability == KSolverStatus.SAT)
//                println(satisfiability) // SAT
                // obtain model
//                val model: Map<String, UInt> = solver.model
//                for ((variable, value) in model) {
//                    println("$variable = $value")
//                }
            }
            println("It took $timeInMillis ms to find a solution")
        }
        return@with timeInMillis
    }
