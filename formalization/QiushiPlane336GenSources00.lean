import QiushiPlane336GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit231Dispatch
import QiushiWcOrbit179Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit233Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane336GenSource0000 :
    QuotientRankAtLeast (spanCodes [256, 98, 16, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 84, 32, 10, 1] [(256, 128), (98, 84), (16, 32), (12, 10), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit179_lb15_wc

theorem plane336GenSource0001 :
    QuotientRankAtLeast (spanCodes [256, 98, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 384), (98, 116), (16, 32), (14, 10), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane336GenSource0002 :
    QuotientRankAtLeast (spanCodes [256, 76, 46, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 32), (76, 10), (46, 126), (16, 384), (1, 1)]
    (codeMat 305) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane336GenSource0003 :
    QuotientRankAtLeast (spanCodes [256, 132, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 84, 32, 10, 1] [(256, 1), (132, 10), (98, 84), (16, 128), (1, 32)]
    (codeMat 140) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit179_lb15_wc

theorem plane336GenSource0004 :
    QuotientRankAtLeast (spanCodes [256, 136, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 84, 32, 10, 1] [(256, 32), (136, 10), (98, 84), (16, 1), (1, 128)]
    (codeMat 98) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit179_lb15_wc

theorem plane336GenSource0005 :
    QuotientRankAtLeast (spanCodes [256, 138, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 384), (138, 10), (98, 116), (16, 1), (1, 32)]
    (codeMat 106) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane336GenSource0006 :
    QuotientRankAtLeast (spanCodes [256, 140, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 140, 98, 16, 1] [(256, 1), (140, 98), (98, 140), (16, 16), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit231_lb15_unconditional

theorem plane336GenSource0007 :
    QuotientRankAtLeast (spanCodes [256, 142, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 140, 98, 16, 1] [(256, 260), (142, 140), (98, 99), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit233_lb15_wc

theorem plane336GenSource0008 :
    QuotientRankAtLeast (spanCodes [256, 164, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 1), (164, 10), (98, 116), (16, 32), (1, 384)]
    (codeMat 156) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane336GenSource0009 :
    QuotientRankAtLeast (spanCodes [256, 166, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 1), (166, 126), (98, 116), (16, 384), (1, 32)]
    (codeMat 140) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

end QiushiMatmul
