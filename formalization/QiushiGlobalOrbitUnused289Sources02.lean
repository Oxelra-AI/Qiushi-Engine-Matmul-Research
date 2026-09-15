import QiushiGlobalOrbitUnused289Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane289UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 22), (128, 2), (64, 1), (18, 128), (10, 91), (6, 54), (1, 9)]
    (codeMat 236) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane289UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 434), (160, 162), (66, 77), (18, 256), (10, 69), (6, 2), (1, 1)]
    (codeMat 241) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane289UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 322), (128, 128), (68, 69), (34, 42), (20, 21), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane289UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 91), (130, 128), (68, 10), (38, 100), (20, 329), (10, 69), (1, 1)]
    (codeMat 233) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane289UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 323), (132, 197), (68, 69), (38, 43), (20, 30), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane289UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 148), (128, 288), (64, 216), (34, 20), (16, 32), (10, 28), (4, 2), (1, 3)]
    (codeMat 401) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane289UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 150), (130, 288), (64, 219), (34, 20), (16, 32), (10, 28), (4, 2), (1, 3)]
    (codeMat 465) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
