import QiushiPlane457GenData
import QiushiCertifiedTransport
import QiushiStep133Mono393From243
import QiushiStep133Mono397From243
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit194Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane457GenSource0010 :
    QuotientRankAtLeast (spanCodes [259, 194, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(259, 153), (194, 10), (20, 243), (10, 30)]
    (codeMat 421) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane457GenSource0011 :
    QuotientRankAtLeast (spanCodes [262, 199, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(262, 10), (199, 20), (20, 80), (10, 328)]
    (codeMat 141) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane457GenSource0012 :
    QuotientRankAtLeast (spanCodes [293, 228, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(293, 135), (228, 231), (20, 243), (10, 237)]
    (codeMat 309) (codeMat 470) (codeMat 213) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane457GenSource0013 :
    QuotientRankAtLeast (spanCodes [294, 231, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(294, 90), (231, 20), (20, 80), (10, 280)]
    (codeMat 157) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane457GenSource0014 :
    QuotientRankAtLeast (spanCodes [449, 33, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(449, 100), (33, 52), (20, 42), (8, 32), (2, 63)]
    (codeMat 275) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane457GenSource0015 :
    QuotientRankAtLeast (spanCodes [449, 35, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(449, 80), (35, 62), (17, 21), (10, 42), (5, 32)]
    (codeMat 266) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane457GenSource0016 :
    QuotientRankAtLeast (spanCodes [389, 68, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(389, 133), (68, 263), (20, 11), (8, 32), (2, 1)]
    (codeMat 337) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane457GenSource0017 :
    QuotientRankAtLeast (spanCodes [388, 69, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(388, 133), (69, 263), (20, 42), (9, 32), (3, 1)]
    (codeMat 345) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane457GenSource0018 :
    QuotientRankAtLeast (spanCodes [390, 70, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(390, 27), (70, 11), (20, 326), (10, 69), (1, 1)]
    (codeMat 161) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane457GenSource0019 :
    QuotientRankAtLeast (spanCodes [417, 96, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(417, 142), (96, 316), (20, 11), (8, 32), (2, 1)]
    (codeMat 465) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
