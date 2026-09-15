import QiushiPlane434GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit293From196
import QiushiMonoOrbit311From196
import QiushiMonoOrbit340From196
import QiushiStep128Mono343From214
import QiushiStep128Mono346From214T
import QiushiWcOrbit194Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane434GenSource0010 :
    QuotientRankAtLeast (spanCodes [266, 136, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(266, 142), (136, 10), (16, 1), (1, 32)]
    (codeMat 98) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane434GenSource0011 :
    QuotientRankAtLeast (spanCodes [262, 132, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(262, 132), (132, 262), (16, 32), (12, 10), (1, 1)]
    (codeMat 337) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane434GenSource0012 :
    QuotientRankAtLeast (spanCodes [266, 162, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(266, 107), (162, 10), (16, 1), (1, 384)]
    (codeMat 442) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane434GenSource0013 :
    QuotientRankAtLeast (spanCodes [266, 164, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(266, 359), (164, 100), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane434GenSource0014 :
    QuotientRankAtLeast (spanCodes [266, 166, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(266, 298), (166, 100), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane434GenSource0015 :
    QuotientRankAtLeast (spanCodes [266, 168, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(266, 107), (168, 10), (16, 1), (1, 384)]
    (codeMat 114) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane434GenSource0016 :
    QuotientRankAtLeast (spanCodes [266, 174, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(266, 461), (174, 116), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane434GenSource0017 :
    QuotientRankAtLeast (spanCodes [266, 196, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(266, 359), (196, 100), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane434GenSource0018 :
    QuotientRankAtLeast (spanCodes [266, 198, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(266, 298), (198, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane434GenSource0019 :
    QuotientRankAtLeast (spanCodes [266, 206, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(266, 461), (206, 116), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

end QiushiMatmul
