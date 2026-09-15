import QiushiGlobalOrbitUnused386Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane386UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [294, 161, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(294, 136), (161, 339), (68, 295), (20, 232), (10, 430)]
    (codeMat 382) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane386UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [295, 161, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(295, 338), (161, 339), (68, 295), (20, 463), (10, 430)]
    (codeMat 405) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane386UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [262, 160, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 262), (160, 160), (68, 68), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane386UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [128, 68, 32, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(128, 128), (68, 68), (32, 32), (20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane386UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [132, 68, 36, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(132, 100), (68, 68), (36, 128), (20, 91), (8, 3), (2, 9), (1, 1)]
    (codeMat 281) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane386UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 16), (160, 160), (64, 2), (16, 256), (10, 68), (4, 8), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane386UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 440), (160, 168), (66, 71), (18, 256), (10, 69), (6, 8), (1, 1)]
    (codeMat 241) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane386UnusedGenSource0017 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 256), (64, 128), (32, 8), (16, 32), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane386UnusedGenSource0018 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 199), (130, 256), (64, 130), (34, 28), (16, 32), (10, 20), (4, 3), (1, 2)]
    (codeMat 337) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane386UnusedGenSource0019 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 504), (128, 288), (66, 148), (32, 63), (18, 32), (10, 22), (6, 3), (1, 2)]
    (codeMat 473) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
