import QiushiStep131Orbit451ScalarDispatchV2

set_option linter.unusedVariables false

namespace QiushiMatmul

/-- Clean downstream-facing alias for the repaired and audited orbit451 quotient lower bound.
It states the quotient space explicitly as `spanCodes [257,19,10]`, avoiding any
ambiguity about the definition of `o451W`. -/
theorem step132_orbit451_span257_19_10_lb18 :
    QuotientRankAtLeast (spanCodes [257, 19, 10]) 18 := by
  exact step126_orbit451_lb18

end QiushiMatmul
