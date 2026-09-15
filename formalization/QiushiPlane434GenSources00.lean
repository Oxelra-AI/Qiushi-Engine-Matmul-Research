import QiushiPlane434GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit293From196
import QiushiMonoOrbit311From196
import QiushiMonoOrbit340From196
import QiushiStep128Mono343From214
import QiushiStep128Mono346From214T
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit281Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane434GenSource0000 :
    QuotientRankAtLeast (spanCodes [256, 16, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(256, 256), (16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane434GenSource0001 :
    QuotientRankAtLeast (spanCodes [262, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(262, 132), (16, 32), (12, 10), (1, 1)]
    (codeMat 337) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane434GenSource0002 :
    QuotientRankAtLeast (spanCodes [266, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(266, 142), (34, 10), (16, 1), (1, 32)]
    (codeMat 394) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane434GenSource0003 :
    QuotientRankAtLeast (spanCodes [266, 66, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(266, 142), (66, 10), (16, 32), (1, 1)]
    (codeMat 161) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane434GenSource0004 :
    QuotientRankAtLeast (spanCodes [266, 70, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(266, 107), (70, 10), (16, 384), (1, 1)]
    (codeMat 169) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane434GenSource0005 :
    QuotientRankAtLeast (spanCodes [266, 76, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(266, 107), (76, 10), (16, 384), (1, 1)]
    (codeMat 377) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane434GenSource0006 :
    QuotientRankAtLeast (spanCodes [266, 66, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(266, 142), (66, 268), (34, 10), (16, 1), (1, 32)]
    (codeMat 394) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane434GenSource0007 :
    QuotientRankAtLeast (spanCodes [266, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(266, 359), (100, 100), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane434GenSource0008 :
    QuotientRankAtLeast (spanCodes [266, 108, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(266, 335), (108, 100), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane434GenSource0009 :
    QuotientRankAtLeast (spanCodes [266, 110, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(266, 461), (110, 116), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

end QiushiMatmul
