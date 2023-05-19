package sls.solver

import org.ksmt.KContext
import org.ksmt.decl.KConstDecl
import org.ksmt.expr.KExpr
import org.ksmt.solver.KModel
import org.ksmt.solver.KSolver
import org.ksmt.solver.KSolverStatus
import org.ksmt.sort.KBoolSort
import kotlin.math.log2
import kotlin.math.max
import kotlin.math.sqrt
import kotlin.random.Random
import kotlin.random.nextUInt
import kotlin.time.Duration

@Suppress("EnumEntryName")
open class SLSLover(private val ctx: KContext) : KSolver<SLSSolverConfiguration> {
    private var formula: MutableList<AST> = mutableListOf()
    private var allVariables: HashMap<String, UInt> = hashMapOf()
    private var allBoolVariables: HashSet<String> = hashSetOf()
    private var variablesMap: HashMap<AST, HashSet<String>> = hashMapOf()
    private var affectedConstraints: HashMap<String, HashSet<AST>> = hashMapOf()
    public var model: HashMap<String, UInt> = hashMapOf()

    @Suppress("SpellCheckingInspection")
    sealed class Node {
        enum class OpSealed {
            eq, and, or, not, bvnot, bvult, bvule, bvshl, bvshr, bvadd, bvand, bvmul,
            bvudiv, bvurem, concat, extract
        }

        data class Op(val op: OpSealed) : Node()
        data class BvConst(val v: UInt) : Node()
        data class BvVar(val v: String) : Node()
        data class BoolVar(val v: String) : Node()
    }

    private inner class AST(val node: Node) {
        var lhs: AST? = null
        var rhs: AST? = null

        constructor(node: Node, lhsOuter: AST) : this(node) {
            lhs = lhsOuter
        }

        constructor(node: Node, lhsOuter: AST, rhsOuter: AST) : this(node, lhsOuter) {
            rhs = rhsOuter
        }
    }

    private inner class Checker {
        /* constants */
        private val bw: Int = 32 // bit-width of bitvectors
        private val wp: Double = .1 // random walk probability
        private val sp: Double = .95 // random walk probability
        private var maxTries: UInt = 1000u
        private var c1: Double = .5
        private var c2: UInt = 50u
        private var c3: Int = 20
        private val m: Int = formula.size

        /* state of solver */
        var score: Double = .0
        var alpha: HashMap<String, UInt> = hashMapOf() // assignment
        var weights: HashMap<AST, Double> = hashMapOf()
        var scores: HashMap<AST, Double> = hashMapOf()
        var selected: HashMap<AST, Int> = hashMapOf()
        var isRandomizedLastMove: Boolean = false
        var nMoves: Int = 0

        private fun initInputs() {
            for (variable in allVariables.keys) {
                alpha[variable] = 0u
            }
        }

        private fun eval(ast: AST): UInt {
            return when (ast.node) {
                is Node.BoolVar -> inaccessible()
                is Node.BvConst -> ast.node.v
                is Node.BvVar -> alpha[ast.node.v]!!
                is Node.Op -> {
                    when (ast.node.op) {
                        Node.OpSealed.bvnot -> eval(ast.lhs!!).inv()
                        Node.OpSealed.bvshl -> eval(ast.lhs!!) shl eval(ast.rhs!!).toInt()
                        Node.OpSealed.bvshr -> eval(ast.lhs!!) shr eval(ast.rhs!!).toInt()
                        Node.OpSealed.bvadd -> eval(ast.lhs!!) + eval(ast.rhs!!)
                        Node.OpSealed.bvand -> eval(ast.lhs!!) and eval(ast.rhs!!)
                        Node.OpSealed.bvmul -> eval(ast.lhs!!) * eval(ast.rhs!!)
                        Node.OpSealed.bvudiv -> eval(ast.lhs!!) / eval(ast.rhs!!)
                        Node.OpSealed.bvurem -> eval(ast.lhs!!) % eval(ast.rhs!!)
                        Node.OpSealed.concat -> TODO("Cannot be implemented")
                        Node.OpSealed.extract -> TODO("Cannot be implemented")

                        else -> inaccessible()
                    }
                }
            }
        }

        private fun hammingDistance(a: UInt, b: UInt): Int {
            return a.xor(b).countOneBits()
        }

        fun getBit(value: UInt, position: Int): UInt {
            return (value shr position) and 1u
        }

        // heuristic to find upper bound for number of flipped bits in $a s.t. $a < $b
        private fun minFlips(a: UInt, b: UInt): Int {
            if (b == 0u) return hammingDistance(a, b)

            var tmp: UInt = a
            var res = 0
            var i = 0
            var j: Int = bw - 1
            while (i < bw) {
                if (getBit(tmp, j) == 0u) {
                    i++
                    j--
                    continue
                }

                res++
                tmp -= (1u shr j)
                if (tmp < b) break

                i++
                j--
            }

            return res
        }

        private fun nodeOpHandler(node: Node.Op, lhs: AST?, rhs: AST?): Double {
            when (node.op) {
                Node.OpSealed.not -> {
                    val underNot: AST = lhs!!
                    when (underNot.node) {
                        is Node.BoolVar -> return alpha[underNot.node.v]!!.toDouble()
                        is Node.Op -> {
                            return when (underNot.node.op) {
                                Node.OpSealed.and -> {
                                    // s(!(a && b)) = max(s(!a), s(!b))
                                    val notA = AST(Node.Op(Node.OpSealed.not), underNot.lhs!!)
                                    val notB = AST(Node.Op(Node.OpSealed.not), underNot.rhs!!)
                                    max(computeScoreConstraint(notA), computeScoreConstraint(notB))
                                }

                                Node.OpSealed.eq -> if (eval(underNot.lhs!!) != eval(underNot.rhs!!)) 1.0 else .0
                                Node.OpSealed.bvult -> {
                                    val evaluatedLhs: UInt = eval(underNot.lhs!!)
                                    val evaluatedRhs: UInt = eval(underNot.rhs!!)
                                    return if (evaluatedLhs >= evaluatedRhs) 1.0
                                    else c1 * (1 - minOf(
                                        minFlips(evaluatedRhs, evaluatedLhs),
                                        hammingDistance(evaluatedLhs, evaluatedRhs)
                                    ) / 32)
                                }

                                else -> inaccessible()
                            }
                        }

                        is Node.BvVar -> inaccessible()
                        is Node.BvConst -> inaccessible()
                    }
                }

                Node.OpSealed.and -> {
                    return (computeScoreConstraint(lhs!!) + computeScoreConstraint(rhs!!)) * .5f
                }

                Node.OpSealed.eq -> {
                    val evaluatedLhs: UInt = eval(lhs!!)
                    val evaluatedRhs: UInt = eval(rhs!!)
                    return if (evaluatedLhs == evaluatedRhs) 1.0
                    else c1 * (1 - hammingDistance(evaluatedLhs, evaluatedRhs) / 32)
                }

                Node.OpSealed.or -> {
                    return max(computeScoreConstraint(lhs!!), computeScoreConstraint(rhs!!))
                }

                Node.OpSealed.bvult -> {
                    val evaluatedLhs: UInt = eval(lhs!!)
                    val evaluatedRhs: UInt = eval(rhs!!)
                    return if (evaluatedLhs < evaluatedRhs) 1.0
                    else c1 * (1 - minFlips(evaluatedLhs, evaluatedRhs) / 32)
                }

                Node.OpSealed.bvule -> {
                    return max(
                        computeScoreConstraint(AST(Node.Op(Node.OpSealed.eq), lhs!!, rhs!!)),
                        computeScoreConstraint(AST(Node.Op(Node.OpSealed.bvult), lhs, rhs))
                    )
                }

                else -> inaccessible()
            }
        }

        private fun computeScoreConstraint(constraint: AST): Double {
            return when (constraint.node) {
                is Node.BoolVar -> alpha[constraint.node.v]!!.toDouble()
                is Node.BvVar -> inaccessible()
                is Node.Op -> nodeOpHandler(constraint.node, constraint.lhs, constraint.rhs)
                is Node.BvConst -> inaccessible()
            }
        }

        private fun inaccessible(): Nothing {
            throw UnsupportedOperationException("This code block should be inaccessible")
        }

        private fun computeScore() {
            score = .0
            for ((constraint, weight) in weights) {
                scores[constraint] = computeScoreConstraint(constraint)
                score += weight * scores[constraint]!!
            }
        }

        private fun maxMoves(i: UInt): UInt {
            return if (i % 2u == 0u) {
                c2 * (1u shl i.toInt()) / 2u
            } else {
                c2
            }
        }

        private fun isSat(constraint: AST): Boolean {
            return scores[constraint]!! == 1.0
        }

        private fun allConstraintsSat(): Boolean {
            return formula.all { constraint -> isSat(constraint) }
        }

        private fun updateAssignments(variable: String, value: UInt) {
            alpha[variable] = value
        }

        private fun init() {
            formula.forEach { constraint -> weights[constraint] = 1.0 }
            for (constraint in formula) {
                selected[constraint] = 0
                scores[constraint] = .0
            }
        }

        private fun selectConstraint(): AST {
            var maximized = -1.0
            var ans: AST? = null
            for (constraint in formula) {
                if (isSat(constraint)) continue

                val currentConstraintScore: Double =
                    scores[constraint]!! + c3 * sqrt(log2(selected[constraint]!!.toDouble()) / nMoves)
                if (ans == null || maximized < currentConstraintScore) {
                    maximized = currentConstraintScore
                    ans = constraint
                    selected[constraint] = selected[constraint]!! + 1
                }
            }
            return ans!!
        }

        private fun hasNonCostInput(root: AST?): Boolean {
            if (root == null) return false
            if (root.node is Node.BvVar) return true
            if (root.node is Node.BoolVar) return true
            return hasNonCostInput(root.lhs) || hasNonCostInput(root.rhs)
        }

        private fun getExactlyOneCtrlInputOrRandom(root: AST): AST {
            assert(root.node is Node.Op && root.node.op == Node.OpSealed.and)
            val controls: MutableList<AST> = mutableListOf()

            fun collectControlInputs(constraint: AST) {
                when (val node = constraint.node) {
                    is Node.Op -> {
                        when (node.op) {
                            Node.OpSealed.and -> {
                                collectControlInputs(constraint.lhs!!)
                                collectControlInputs(constraint.rhs!!)
                            }

                            else -> {
                                if (computeScoreConstraint(constraint) != 1.0) {
                                    controls.add(constraint)
                                }
                            }
                        }
                    }

                    else -> inaccessible()
                }
            }

            collectControlInputs(root)
            return controls.random()
        }

        private fun gcd(a: Long, b: Long): Long {
            var num1 = a
            var num2 = b

            while (num2 != 0L) {
                val temp = num2
                num2 = num1 % num2
                num1 = temp
            }

            return num1
        }

        private fun computeValue(cur: AST, other: AST?, value: UInt): UInt? {
            val evaluatedOther: UInt? = if (other != null) eval(other) else null
            val uIntMax: UInt = (-1).toUInt()
            when (cur.node) {
                is Node.Op -> {
                    return when (cur.node.op) {
                        Node.OpSealed.eq -> {
                            if (value == 1u) evaluatedOther
                            else {
                                var random: UInt = Random.nextUInt()
                                while (random != evaluatedOther) random = Random.nextUInt()
                                random
                            }
                        }

                        Node.OpSealed.bvnot -> {
                            value.inv()
                        }

                        Node.OpSealed.bvult -> {
                            if (cur.lhs!! == other!!) {
                                if (value == 1u && evaluatedOther!! < uIntMax) {
                                    var random: UInt = Random.nextUInt()
                                    while (random <= evaluatedOther)
                                        random = Random.nextUInt()
                                    random
                                } else if (value == 0u) {
                                    var random: UInt = Random.nextUInt()
                                    while (random > evaluatedOther!!)
                                        random = Random.nextUInt()
                                    random
                                } else if (other.node !is Node.BvConst) {
                                    var random: UInt = Random.nextUInt()
                                    while (random == 0u)
                                        random = Random.nextUInt()
                                    random
                                } else {
                                    null
                                }
                            } else {
                                if (value == 1u && evaluatedOther!! != 0u) {
                                    var random: UInt = Random.nextUInt()
                                    while (random >= evaluatedOther)
                                        random = Random.nextUInt()
                                    random
                                } else if (value == 0u) {
                                    var random: UInt = Random.nextUInt()
                                    while (random < evaluatedOther!!)
                                        random = Random.nextUInt()
                                    random
                                } else if (other.node !is Node.BvConst) {
                                    var random: UInt = Random.nextUInt()
                                    while (random == uIntMax)
                                        random = Random.nextUInt()
                                    random
                                } else {
                                    null
                                }
                            }
                        }

                        Node.OpSealed.bvule -> {
                            if (cur.lhs!! == other!!) {
                                if (value == 1u) {
                                    var random: UInt = Random.nextUInt()
                                    while (random < evaluatedOther!!)
                                        random = Random.nextUInt()
                                    random
                                } else if (value == 0u && evaluatedOther!! != 0u) {
                                    var random: UInt = Random.nextUInt()
                                    while (random >= evaluatedOther)
                                        random = Random.nextUInt()
                                    random
                                } else if (other.node !is Node.BvConst) {
                                    Random.nextUInt()
                                } else {
                                    null
                                }
                            } else {
                                if (value == 1u) {
                                    var random: UInt = Random.nextUInt()
                                    while (random > evaluatedOther!!)
                                        random = Random.nextUInt()
                                    random
                                } else if (value == 0u && evaluatedOther!! < uIntMax) {
                                    var random: UInt = Random.nextUInt()
                                    while (random <= evaluatedOther)
                                        random = Random.nextUInt()
                                    random
                                } else if (other.node !is Node.BvConst) {
                                    Random.nextUInt()
                                } else {
                                    null
                                }
                            }
                        }

                        Node.OpSealed.bvshl -> {
                            var cnt = 0
                            while (value and (1u shl cnt) == 0u) cnt++
                            if (cur.lhs!! == other!!) {
                                if (evaluatedOther!! shl cnt != value) null
                                else cnt.toUInt()
                            } else {
                                if (other.node is Node.BvConst && cnt.toUInt() < evaluatedOther!!) null
                                else value shr evaluatedOther!!.toInt()
                            }
                        }

                        Node.OpSealed.bvshr -> {
                            var cnt = 0
                            while (value and ((1u shl 31) shr cnt) == 0u) cnt++
                            if (cur.lhs!! == other!!) {
                                if (evaluatedOther!! shr cnt != value) null
                                else cnt.toUInt()
                            } else {
                                if (other.node is Node.BvConst && cnt.toUInt() < evaluatedOther!!) null
                                else value shl evaluatedOther!!.toInt()
                            }
                        }

                        Node.OpSealed.bvadd -> {
                            value - evaluatedOther!!
                        }

                        Node.OpSealed.bvand -> {
                            if (other!!.node is Node.BvConst && (evaluatedOther!! and value != value)) null
                            else value
                        }

                        Node.OpSealed.bvmul -> {
                            if (value % evaluatedOther!! == 0u) {
                                value / evaluatedOther
                            } else if (gcd(evaluatedOther.toLong(), 1L shl 32) == 1L) {
                                var inverse = 1L
                                while (inverse < 1L shl 32) {
                                    if ((evaluatedOther.toLong() * inverse) % (1L shl 32) == 1L) {
                                        break
                                    }
                                    inverse++
                                }
                                inverse.toUInt() * evaluatedOther
                            } else if (other!!.node !is Node.BvConst) {
                                if (value % 7u == 0u)
                                    value / 7u
                                else if (value % 5u == 0u)
                                    value / 5u
                                else if (value % 3u == 0u)
                                    value / 3u
                                else if (value % 2u == 0u)
                                    value / 2u
                                else
                                    1u
                            } else {
                                null
                            }
                        }

                        Node.OpSealed.bvudiv -> {
                            if (cur.lhs!! == other!!) {
                                if (evaluatedOther!! == 0u && value == 0u) {
                                    Random.nextUInt()
                                } else if (evaluatedOther != 0u && evaluatedOther % value == 0u) {
                                    evaluatedOther / value
                                } else if (other.node !is Node.BvConst) {
                                    Random.nextUInt(uIntMax / value)
                                } else {
                                    null
                                }
                            } else {
                                if (evaluatedOther!! == 0u && value == uIntMax) {
                                    uIntMax
                                } else if (evaluatedOther != 0u && evaluatedOther < uIntMax / value) {
                                    value * evaluatedOther
                                } else if (other.node !is Node.BvConst) {
                                    Random.nextUInt(uIntMax / value) * value
                                } else {
                                    null
                                }
                            }
                        }

                        Node.OpSealed.bvurem -> {
                            if (cur.lhs!! == other!!) {
                                if (evaluatedOther!! == value && evaluatedOther != uIntMax) {
                                    var random: UInt = Random.nextUInt()
                                    while (random <= evaluatedOther)
                                        random = Random.nextUInt()
                                    random
                                } else if (evaluatedOther > value && evaluatedOther - value > value) {
                                    evaluatedOther - value
                                } else if (other.node !is Node.BvConst &&
                                    ((evaluatedOther > value && evaluatedOther - value <= value) ||
                                            (evaluatedOther < value && value < uIntMax))
                                ) {
                                    var random: UInt = Random.nextUInt()
                                    while (random <= value)
                                        random = Random.nextUInt()
                                    random
                                } else {
                                    null
                                }
                            } else {
                                if (evaluatedOther!! > value) {
                                    if (Random.nextBoolean() || evaluatedOther >= uIntMax - value) {
                                        value
                                    } else {
                                        value + Random.nextUInt((uIntMax - value) / evaluatedOther) * evaluatedOther
                                    }
                                } else if (evaluatedOther <= value && other.node !is Node.BvConst) {
                                    value
                                } else {
                                    null
                                }
                            }
                        }

                        Node.OpSealed.concat -> TODO("Cannot be implemented")
                        Node.OpSealed.extract -> TODO("Cannot be implemented")

                        Node.OpSealed.not -> inaccessible()
                        Node.OpSealed.and -> inaccessible()
                        Node.OpSealed.or -> inaccessible()
                    }
                }

                else -> inaccessible()
            }
        }

        private fun selectPropMove(root: AST): Pair<String, UInt> {
            var cur: AST = root
            var value: UInt? = 1u
            while (true) {
                if (cur.node is Node.BvVar) return Pair((cur.node as Node.BvVar).v, value!!)

                // conflict
                if (!hasNonCostInput(cur)) return selectSlsMove(root)

                // path selection
                // if is_ite(cur) {..} TODO

                val input: AST
                if (cur.node is Node.Op && (cur.node as Node.Op).op == Node.OpSealed.and) {
                    input = getExactlyOneCtrlInputOrRandom(cur)
                    if (input.node is Node.Op && input.node.op == Node.OpSealed.or) {
                        cur = input
                        continue
                    }
                    if (input.node is Node.Op && input.node.op == Node.OpSealed.not) {
                        cur = input.lhs!!
                        value = 0u
                        continue
                    }
                    cur = input
                    continue
                } else {
                    input =
                        if (cur.rhs != null)
                            if (Random.nextBoolean()) cur.rhs!!
                            else cur.lhs!!
                        else cur.lhs!!
                }
                // path propagation
                if (input.node is Node.Op && input.node.op == Node.OpSealed.or) {
                    cur = input
                    continue
                }
                if (input.node is Node.Op && input.node.op == Node.OpSealed.not) {
                    cur = input.lhs!!
                    value = 0u
                    continue
                }

                if (input.node is Node.BvConst) return selectSlsMove(root)

                val other: AST? = if (cur.rhs != null) {
                    if (cur.rhs == input) cur.lhs!!
                    else cur.rhs!!
                } else {
                    null
                }
                value = computeValue(cur, other, value!!)

                if (value == null) return selectSlsMove(root)

                cur = input
            }
        }

        private fun randomWalk(vars: Set<String>): Pair<String, UInt> {
            var randomVar: String = vars.random()
            while (allBoolVariables.contains(randomVar)) randomVar = vars.random()

            return Pair(
                randomVar,
                getValueByMove(alpha[randomVar]!!, move = Random.nextInt(0, bw + 3))
            )
        }

        private fun getValueByMove(x: UInt, move: Int): UInt {
            return when (move) {
                (bw + 2) -> x.inv()         // bitwise negation
                (bw + 1) -> x - 1u          // decrement
                (bw + 0) -> x + 1u          // increment
                else -> x xor (1u shl move) // bit flip
            }
        }

        private fun neighbour(x: UInt): List<UInt> {
            return (0..bw + 2).map { move -> getValueByMove(x, move) }
        }

        private fun findBestMove(vars: Set<String>): Pair<String, UInt>? {
            var ans: Pair<String, UInt>? = null
            var maximizedScore: Double = score
            for (variable in vars) {
                val initialValue: UInt = alpha[variable]!!
                for (value in neighbour(alpha[variable]!!)) {
                    val scoresCopy: MutableMap<AST, Double> = scores.toMutableMap()
                    alpha[variable] = value
                    for (constraint in affectedConstraints[variable]!!)
                        scoresCopy[constraint] = computeScoreConstraint(constraint)
                    val newScore: Double =
                        weights.map { (constraint, weight) -> weight * scoresCopy[constraint]!! }
                            .sum()
                    if (newScore > maximizedScore) {
                        ans = Pair(variable, value)
                        maximizedScore = newScore
                    }
                }
                alpha[variable] = initialValue
            }
            return ans
        }

        private fun randomize(vars: Set<String>): Pair<String, UInt> {
            isRandomizedLastMove = true
            val variable = vars.random()
            return Pair(variable, getValueByMove(alpha[variable]!!, Random.nextInt(bw + 3)))
        }

        private fun selectSlsMove(root: AST): Pair<String, UInt> {
            val vars: Set<String> = variablesMap.getValue(root)
            return if (Random.nextDouble() < wp) {
                randomWalk(vars)
            } else {
                findBestMove(vars) ?: randomize(vars)
            }
        }

        private fun selectMove(root: AST): Pair<String, UInt> {
            return if (Random.nextInt(bw + m) < bw) {
                selectPropMove(root)
            } else {
                selectSlsMove(root)
            }
        }

        private fun updateScore(variable: String) {
            for (constraint in affectedConstraints[variable]!!) {
                scores[constraint] = computeScoreConstraint(constraint)
            }
            score = weights.map { (constraint, weight) -> weight * scores[constraint]!! }.sum()
        }

        private fun updateConstraintWeights() {
            if (Random.nextDouble() < sp)
                formula.filter { constraint -> !isSat(constraint) }
                    .forEach { constraint -> weights[constraint] = weights[constraint]!! + 1.0 }
        }

        fun check(): KSolverStatus {
            init()
            for (i in 1u..maxTries) {
                initInputs()
                computeScore()
                for (j in 0u until maxMoves(i)) {
                    if (allConstraintsSat()) {
                        model = alpha
                        return KSolverStatus.SAT
                    }

                    nMoves++
                    val root: AST = selectConstraint()
                    val (variable: String, value: UInt) = selectMove(root)
                    updateAssignments(variable, value)
                    if (isRandomizedLastMove) {
                        isRandomizedLastMove = false
                        updateConstraintWeights()
                    }
                    updateScore(variable)
                }
            }

            return KSolverStatus.UNKNOWN
        }
    }

    private fun binaryStringToUInt(binaryString: CharSequence): UInt {
        val binaryDigits =
            binaryString.subSequence(2, binaryString.length) // Remove the '#b' prefix

        var result = 0u
        for (i in binaryDigits.indices) {
            val digit = binaryDigits[binaryDigits.length - 1 - i]
            if (digit == '1') {
                result += 1u shl i
            }
        }
        return result
    }

    private fun makeAST(
        str: CharSequence,
        canBeBool: Boolean = false,
        inNotOr: Boolean = false,
        op: Node.Op? = null
    ): AST {
        if (!str.contains(' ')) { /* single variable or value */
            if (str[0] == '#') return AST(Node.BvConst(binaryStringToUInt(str.toString())))
            allVariables[str.toString()] = 1u + allVariables.getOrDefault(str, 0u)
            if (canBeBool) {
                allBoolVariables.add(str.toString())
                return AST(Node.BoolVar(str.toString()))
            }
            return AST(Node.BvVar(str.toString()))
        }

        val withoutParenthesis: CharSequence = str.subSequence(1, str.length - 1)
        fun splitAtIndices(input: CharSequence, indices: List<Int>): MutableList<CharSequence> {
            val substrings = mutableListOf<CharSequence>()
            var startIndex = 0
            for (index in indices) {
                substrings.add(input.subSequence(startIndex, index))
                startIndex = index + 1
            }
            // Add the remaining substring
            substrings.add(input.subSequence(startIndex, input.length))
            return substrings
        }

        val indices: MutableList<Int> = mutableListOf()
        var countBrackets = 0
        for (i in withoutParenthesis.indices) {
            if (withoutParenthesis[i] == ' ' && countBrackets == 0) indices.add(i)
            else if (withoutParenthesis[i] == '(') countBrackets += 1
            else if (withoutParenthesis[i] == ')') countBrackets -= 1
        }
        val lst: MutableList<CharSequence> = splitAtIndices(withoutParenthesis, indices)
        if (inNotOr) {
            assert(lst[0] == "or")
            lst[0] = "and"
            for (i in 1..lst.size)
                lst[i] = "(not" + lst[i] + ")"
        }
        val res: AST
        if (lst[0] == "or" || lst[0] == "and") {
            fun helper(helperLst: List<CharSequence>): AST {
                if (helperLst.size == 1) return makeAST(helperLst[0], true)

                val helperRes = AST(Node.Op(Node.OpSealed.valueOf(lst[0].toString())))
                helperRes.lhs = helper(helperLst.subList(0, helperLst.size / 2))
                helperRes.rhs = helper(helperLst.subList(helperLst.size / 2, helperLst.size))
                return helperRes
            }
            res = helper(lst.subList(1, lst.size))
        } else if (lst[0] == "not" && lst[1].startsWith("(bvule")) {
            assert(lst.size == 2)
            res = AST(
                Node.Op(Node.OpSealed.and),
                AST(
                    Node.Op(Node.OpSealed.not),
                    makeAST(lst[1], op = Node.Op(Node.OpSealed.bvult))
                ),
                AST(
                    Node.Op(Node.OpSealed.not),
                    makeAST(lst[1], op = Node.Op(Node.OpSealed.eq))
                )
            )
        } else {
            res =
                if (op == null) AST(Node.Op(Node.OpSealed.valueOf(lst[0].toString()))) else AST(op)
            if (lst[0] == "not") {
                assert(lst.size == 2)
                if (lst[1].startsWith("(or")) res.lhs = makeAST(lst[1], inNotOr = true)
                else res.lhs = makeAST(lst[1])
            } else if (lst[0] == "bvnot") {
                assert(lst.size == 2)
                res.lhs = makeAST(lst[1])
            } else {
                assert(lst.size == 3)
                res.lhs = makeAST(lst[1])
                res.rhs = makeAST(lst[2])
            }
        }

        return res
    }

    private fun collectVariables(root: AST, node: AST? = root) {
        if (node == null) return
        when (node.node) {
            is Node.BoolVar -> {
                if (variablesMap[root] != null)
                    variablesMap[root]!!.add(node.node.v)
                else variablesMap[root] = hashSetOf(node.node.v)
                if (affectedConstraints[node.node.v] != null)
                    affectedConstraints[node.node.v]!!.add(root)
                else affectedConstraints[node.node.v] = hashSetOf(root)
            }

            is Node.BvConst -> return
            is Node.BvVar -> {
                if (variablesMap[root] != null)
                    variablesMap[root]!!.add(node.node.v)
                else variablesMap[root] = hashSetOf(node.node.v)
                if (affectedConstraints[node.node.v] != null)
                    affectedConstraints[node.node.v]!!.add(root)
                else affectedConstraints[node.node.v] = hashSetOf(root)
            }

            is Node.Op -> {
                collectVariables(root, node.lhs)
                collectVariables(root, node.rhs)
            }
        }
    }

    override fun assert(expr: KExpr<KBoolSort>) {
        ctx.ensureContextMatch(expr)
        formula.add(makeAST(expr.toString()))
        collectVariables(formula.last())
    }

    override fun assertAndTrack(expr: KExpr<KBoolSort>, trackVar: KConstDecl<KBoolSort>) {
        TODO("Not yet implemented")
    }

    override fun check(timeout: Duration): KSolverStatus {
        val checker = Checker()
        return checker.check()
    }

    override fun checkWithAssumptions(
        assumptions: List<KExpr<KBoolSort>>,
        timeout: Duration
    ): KSolverStatus {
        TODO("Not yet implemented")
    }

    override fun close() {

    }

    override fun configure(configurator: SLSSolverConfiguration.() -> Unit) {
        TODO("Not yet implemented")
    }

    override fun interrupt() {
        TODO("Not yet implemented")
    }

    override fun model(): KModel {
        TODO("Not yet implemented")
    }

    override fun pop(n: UInt) {
        TODO("Not yet implemented")
    }

    override fun push() {
        TODO("Not yet implemented")
    }

    override fun reasonOfUnknown(): String {
        TODO("Not yet implemented")
    }

    override fun unsatCore(): List<KExpr<KBoolSort>> {
        TODO("Not yet implemented")
    }
}