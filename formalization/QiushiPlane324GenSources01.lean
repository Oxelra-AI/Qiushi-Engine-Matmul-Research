import QiushiPlane324GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit121From55
import QiushiMonoOrbit198From77T
import QiushiMonoOrbit221From77
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit143Dispatch
import QiushiWcOrbit165Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane324GenSource0010 :
    QuotientRankAtLeast (spanCodes [266, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(266, 106), (196, 20), (36, 1), (16, 320), (1, 288)]
    (codeMat 99) (codeMat 204) (codeMat 114) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

theorem plane324GenSource0011 :
    QuotientRankAtLeast (spanCodes [268, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 132, 32, 10, 1] [(268, 43), (196, 451), (36, 1), (16, 365), (1, 32)]
    (codeMat 115) (codeMat 158) (codeMat 358) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit198_lb15_mono

theorem plane324GenSource0012 :
    QuotientRankAtLeast (spanCodes [270, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(270, 116), (196, 42), (36, 1), (16, 384), (1, 511)]
    (codeMat 491) (codeMat 205) (codeMat 242) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane324GenSource0013 :
    QuotientRankAtLeast (spanCodes [326, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(326, 350), (196, 399), (36, 1), (16, 16), (1, 36)]
    (codeMat 467) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane324GenSource0014 :
    QuotientRankAtLeast (spanCodes [328, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(328, 209), (196, 398), (36, 1), (16, 36), (1, 16)]
    (codeMat 459) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane324GenSource0015 :
    QuotientRankAtLeast (spanCodes [330, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [330, 196, 36, 16, 1] [(330, 330), (196, 196), (36, 36), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit221_lb15_mono

theorem plane324GenSource0016 :
    QuotientRankAtLeast (spanCodes [334, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [330, 196, 36, 16, 1] [(334, 426), (196, 224), (36, 36), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit221_lb15_mono

theorem plane324GenSource0017 :
    QuotientRankAtLeast (spanCodes [194, 34, 16, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(194, 386), (34, 44), (16, 32), (6, 1), (1, 2)]
    (codeMat 337) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane324GenSource0018 :
    QuotientRankAtLeast (spanCodes [260, 196, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 2, 1] [(260, 3), (196, 452), (36, 2), (16, 432), (1, 32)]
    (codeMat 94) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit143_lb14_wc

theorem plane324GenSource0019 :
    QuotientRankAtLeast (spanCodes [256, 134, 66, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 2), (134, 34), (66, 164), (36, 3), (16, 45), (1, 438)]
    (codeMat 359) (codeMat 95) (codeMat 244) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
