import QiushiGlobalOrbitUnused306Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit35FP
import QiushiPlane315GenBindings00
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane306UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [256, 128, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 128), (96, 20), (10, 96), (4, 1), (1, 8)]
    (codeMat 161) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane306UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (64, 1), (32, 128), (10, 96), (1, 8)]
    (codeMat 140) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane306UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [272, 132, 68, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(272, 245), (132, 430), (68, 170), (36, 320), (10, 160), (1, 16)]
    (codeMat 207) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane306UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [272, 128, 66, 34, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 245), (128, 360), (66, 149), (34, 30), (10, 23), (4, 3), (1, 2)]
    (codeMat 473) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane306UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [272, 130, 64, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 245), (130, 9), (64, 3), (32, 360), (10, 23), (6, 130), (1, 2)]
    (codeMat 461) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane306UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 16), (132, 168), (68, 160), (36, 2), (16, 325), (10, 68), (1, 256)]
    (codeMat 99) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane306UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 184), (132, 168), (70, 416), (38, 327), (16, 325), (10, 68), (1, 256)]
    (codeMat 107) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane306UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [262, 132, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 414), (132, 235), (66, 29), (34, 284), (20, 227), (10, 28), (1, 3)]
    (codeMat 190) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane306UnusedGenSource0028 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 36, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 503), (132, 113), (68, 78), (36, 219), (22, 81), (10, 10), (1, 1)]
    (codeMat 465) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane306UnusedGenSource0029 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 507), (130, 3), (66, 60), (34, 150), (16, 2), (10, 20), (6, 288), (1, 32)]
    (codeMat 87) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
