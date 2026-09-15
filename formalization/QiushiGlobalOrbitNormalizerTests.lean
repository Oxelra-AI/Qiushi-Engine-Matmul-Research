import QiushiGlobalOrbitNormalizer

namespace QiushiMatmul.GlobalOrbit

example : NormalizationCheck [19, 10] [0, 1, 2, 5, 6, 7, 8] := by decide +kernel
example : ¬ NormalizationCheck [19, 10] [] := by decide +kernel
example : SpanCheck [19, 10] [10, 19] [2, 1] [2, 1] := by decide +kernel
example : ¬ SpanCheck [19, 10] [10, 19] [1, 1] [2, 1] := by decide +kernel

#check normalization_sound
#check transition_sound
#check extensions_of_normalized
#print axioms normalization_sound
#print axioms spanCheck_sound
#print axioms transition_sound
#print axioms extensions_of_normalized

end QiushiMatmul.GlobalOrbit
