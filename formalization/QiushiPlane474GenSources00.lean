import QiushiPlane474GenData
import QiushiCertifiedTransport
import QiushiStep107Orbit373Extraction
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit322Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane474GenSource0000 :
    QuotientRankAtLeast (spanCodes [294, 69, 17, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(294, 414), (69, 160), (17, 11), (10, 10)]
    (codeMat 267) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane474GenSource0001 :
    QuotientRankAtLeast (spanCodes [275, 84, 53, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(275, 225), (84, 460), (53, 20), (10, 21)]
    (codeMat 339) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane474GenSource0002 :
    QuotientRankAtLeast (spanCodes [294, 148, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(294, 472), (148, 224), (84, 225), (10, 301)]
    (codeMat 116) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane474GenSource0003 :
    QuotientRankAtLeast (spanCodes [294, 70, 18, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(294, 326), (70, 78), (18, 27), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane474GenSource0004 :
    QuotientRankAtLeast (spanCodes [263, 70, 33, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(263, 497), (70, 350), (33, 42), (18, 32), (10, 33)]
    (codeMat 410) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane474GenSource0005 :
    QuotientRankAtLeast (spanCodes [258, 67, 36, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 408), (67, 435), (36, 32), (23, 278), (10, 434)]
    (codeMat 215) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane474GenSource0006 :
    QuotientRankAtLeast (spanCodes [263, 65, 33, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(263, 497), (65, 1), (33, 42), (21, 341), (10, 506)]
    (codeMat 477) (codeMat 183) (codeMat 419) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane474GenSource0007 :
    QuotientRankAtLeast (spanCodes [274, 80, 48, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(274, 301), (80, 133), (48, 1), (10, 42), (4, 32)]
    (codeMat 266) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane474GenSource0008 :
    QuotientRankAtLeast (spanCodes [272, 81, 51, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(272, 383), (81, 373), (51, 257), (10, 97), (5, 1)]
    (codeMat 225) (codeMat 190) (codeMat 355) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane474GenSource0009 :
    QuotientRankAtLeast (spanCodes [290, 129, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(290, 11), (129, 132), (80, 278), (10, 434), (4, 1)]
    (codeMat 377) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
