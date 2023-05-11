from logic.logic import LogicFunction
import numpy as np

BiggerOrEqual = LogicFunction("BiggerOrEqual", 2)
SmallerOrEqual = LogicFunction("SmallerOrEqual", 2)
Equivalent = LogicFunction("Equivalent", 2)
Bigger = LogicFunction("Bigger", 2)
Smaller = LogicFunction("Smaller", 2)

necessary_logic_functions = {
    "BiggerOrEqual": BiggerOrEqual,
    "SmallerOrEqual": SmallerOrEqual,
    "Equivalent": Equivalent,
    "Bigger": Bigger,
    "Smaller": Smaller
}

numpy_logic_functions = {
    "BiggerOrEqual": np.greater_equal,
    "SmallerOrEqual": np.less_equal,
    "Equivalent": np.equal,
    "Bigger": np.greater,
    "Smaller": np.less
}