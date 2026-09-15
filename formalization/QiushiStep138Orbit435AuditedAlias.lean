import QiushiStep136Orbit435Dispatch

namespace QiushiMatmul

/-- orbit435 quotient-rank lower bound.
    W = spanCodes [193, 19, 10], annihilator dual basis [145, 26, 4, 32, 192, 256].
    63-source weighted cover with λ₀ = 12158280, Σλᵢ = 125635560,
    weighted lb sum = 1860216840, (125635560 - 12158280) × 16 = 1815636480 < 1860216840.
    Quotient-coordinate-correct annihilator basis verified by step137 semantics check. -/
theorem step138_orbit435_span193_19_10_lb17 :
    QuotientRankAtLeast (spanCodes [193, 19, 10]) 17 :=
  step136_orbit435_lb17

end QiushiMatmul
