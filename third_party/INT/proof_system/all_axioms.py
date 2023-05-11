from proof_system.special_axioms import EquivalenceSubstitution
from proof_system.field_axioms import field_axioms
from proof_system.ordered_field_additional_axioms import ordered_field_additional_axioms
from proof_system.theorems import theorems
special_axioms = {
    "EquivalenceSubstitution": EquivalenceSubstitution(),
}

all_axioms = {**field_axioms, **ordered_field_additional_axioms, **special_axioms, **theorems}
all_axioms_to_prove = {**field_axioms, **ordered_field_additional_axioms, **theorems}

generation_type = {
    "AdditionCommutativity": "Equality",
    "AdditionAssociativity": "Equality",
    "AdditionZero": "Equality",
    "AdditionSimplification": "Equality",
    "MultiplicationCommutativity": "Equality",
    "MultiplicationAssociativity": "Equality",
    "MultiplicationOne": "Equality",
    "MultiplicationSimplification": "Equality",
    "AdditionMultiplicationLeftDistribution": "Equality",
    "AdditionMultiplicationRightDistribution": "Equality",
    "SquareDefinition": "Equality",
    "EquivalenceSymmetry": "Equality",
    "PrincipleOfEquality": "Equality",
    "EquMoveTerm": "Equality",
    "IneqMoveTerm": "Inequality",
    "SquareGEQZero": "Transition",
    "EquivalenceImpliesDoubleInequality": "Transition",
    "FirstPrincipleOfInequality": "Inequality",
    "SecondPrincipleOfInequality": "Inequality",
    # new add
    "RootDefinition": "Equality",
    "RootSimplification": "Equality",
    "NegativeDefinition": "Equality",
    "NegativeSimplification": "Equality",
    "MultiplicationZero": "Equality",
    "AMGMInequality": "Inequality",
    "BernoulliInequality": "Inequality",
    "YoungInequality": "Inequality",
    "HolderInequality": "Inequality",
    "ChebyshevSumInequality": "Inequality",
    "ExponentialInequality": "Inequality",
    "MinkowskiInequality": "Inequality",
    "JensenInequality": "Inequality",
    "InverseInequality": "Inequality",
    "SquareRootInequality": "Inequality",
    # "LogInequality": "Inequality",
    "BigtoBiggerInequality": "Inequality",
    "SecondLawOfIneqMoveTerm": "Inequality",
}

axiom_sets = {
    "field": field_axioms,
    "ordered_field": {**field_axioms, **ordered_field_additional_axioms, **theorems},
}
