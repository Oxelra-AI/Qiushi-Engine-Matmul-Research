import QiushiPlane336GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit142From56
import QiushiOrbit10FP
import QiushiOrbit40FP
import QiushiWcOrbit114Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit233Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane336GenSource0010 :
    QuotientRankAtLeast (spanCodes [256, 168, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 32), (168, 10), (98, 116), (16, 1), (1, 384)]
    (codeMat 98) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane336GenSource0011 :
    QuotientRankAtLeast (spanCodes [256, 172, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 140, 98, 16, 1] [(256, 16), (172, 140), (98, 99), (16, 1), (1, 260)]
    (codeMat 226) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit233_lb15_wc

theorem plane336GenSource0012 :
    QuotientRankAtLeast (spanCodes [256, 174, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 140, 98, 16, 1] [(256, 1), (174, 239), (98, 99), (16, 260), (1, 16)]
    (codeMat 396) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit233_lb15_wc

theorem plane336GenSource0013 :
    QuotientRankAtLeast (spanCodes [256, 66, 32, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(256, 8), (66, 160), (32, 1), (16, 2), (1, 256)]
    (codeMat 98) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane336GenSource0014 :
    QuotientRankAtLeast (spanCodes [256, 64, 34, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(256, 2), (64, 1), (34, 160), (16, 256), (1, 8)]
    (codeMat 140) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane336GenSource0015 :
    QuotientRankAtLeast (spanCodes [256, 72, 42, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 2, 1] [(256, 325), (72, 1), (42, 272), (16, 32), (1, 2)]
    (codeMat 142) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit142_lb14_mono

theorem plane336GenSource0016 :
    QuotientRankAtLeast (spanCodes [256, 98, 16, 8, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 128] [(256, 128), (98, 84), (16, 32), (8, 8), (4, 2), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit40_lb12

theorem plane336GenSource0017 :
    QuotientRankAtLeast (spanCodes [256, 128, 98, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 128] [(256, 1), (128, 2), (98, 84), (16, 128), (4, 8), (1, 32)]
    (codeMat 140) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit40_lb12

theorem plane336GenSource0018 :
    QuotientRankAtLeast (spanCodes [256, 128, 98, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 128] [(256, 32), (128, 8), (98, 84), (16, 1), (8, 2), (1, 128)]
    (codeMat 98) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit40_lb12

theorem plane336GenSource0019 :
    QuotientRankAtLeast (spanCodes [256, 132, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (132, 160), (96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
