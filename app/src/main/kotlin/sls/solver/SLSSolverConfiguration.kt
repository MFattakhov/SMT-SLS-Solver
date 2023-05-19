package sls.solver

import org.ksmt.solver.KSolverConfiguration
import org.ksmt.solver.KSolverUniversalConfigurationBuilder
import kotlin.collections.HashMap

interface SLSSolverConfiguration : KSolverConfiguration {
    fun setSLSOption(option: String, value: Boolean)
    fun setSLSOption(option: String, value: Int)
    fun setSLSOption(option: String, value: Double)
    fun setSLSOption(option: String, value: String)

    override fun setBoolParameter(param: String, value: Boolean) {
        setSLSOption(param, value)
    }

    override fun setDoubleParameter(param: String, value: Double) {
        setSLSOption(param, value)
    }

    override fun setIntParameter(param: String, value: Int) {
        setSLSOption(param, value)
    }

    override fun setStringParameter(param: String, value: String) {
        setSLSOption(param, value)
    }
}

class SLSSolverConfigurationImpl() : SLSSolverConfiguration {
    private var intParams: HashMap<String, Int> = HashMap<String, Int> ()
    private var booleanParams: HashMap<String, Boolean> = HashMap<String, Boolean> ()
    private var doubleParams: HashMap<String, Double> = HashMap<String, Double> ()
    private var stringParams: HashMap<String, String> = HashMap<String, String> ()

    override fun setSLSOption(option: String, value: Boolean) {
        booleanParams.put(option, value)
    }

    override fun setSLSOption(option: String, value: Int) {
        intParams.put(option, value)
    }

    override fun setSLSOption(option: String, value: Double) {
        doubleParams.put(option, value)
    }

    override fun setSLSOption(option: String, value: String) {
        stringParams.put(option, value)
    }

    init {

    }
}

class SLSSolverUniversalConfiguration(
    private val builder: KSolverUniversalConfigurationBuilder
) : SLSSolverConfiguration {
    override fun setSLSOption(option: String, value: Boolean) {
        builder.buildBoolParameter(option, value)
    }

    override fun setSLSOption(option: String, value: Int) {
        builder.buildIntParameter(option, value)
    }

    override fun setSLSOption(option: String, value: Double) {
        builder.buildDoubleParameter(option, value)
    }

    override fun setSLSOption(option: String, value: String) {
        builder.buildStringParameter(option, value)
    }
}