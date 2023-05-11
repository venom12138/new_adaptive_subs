from logic.logic import NumericalFunction
from collections import OrderedDict
import numpy as np
np.seterr(all='ignore')

add = NumericalFunction("add", 2) # 加
opp = NumericalFunction("opp", 1) # 取反
mul = NumericalFunction("mul", 2) # 乘
sqr = NumericalFunction("sqr", 1) # 平方
inv = NumericalFunction("inv", 1) # 逆
root = NumericalFunction("root", 1) # 平方根
pow = NumericalFunction("pow", 2) # 指数:a^b
# log = NumericalFunction("log", 1) # 以2为底的对数
necessary_numerical_functions = \
    OrderedDict(
        [("add", add),
        ("opp", opp),
        ("mul", mul),
        ("sqr", sqr),
        ("inv", inv),
        ("root", root),
        ("pow", pow),]
    )
# ("log", log)
    
numpy_numerical_functions = \
    OrderedDict(
        [("add", np.add),
        ("opp", np.negative),
        ("mul", np.multiply),
        ("sqr", np.square),
        ("inv", np.reciprocal), # 类型转换成float
        ("root", np.sqrt),
        ("pow", np.power), ]
    )
# ("log", np.log2)
