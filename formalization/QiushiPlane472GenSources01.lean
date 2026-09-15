import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0010 :
    QuotientRankAtLeast (spanCodes [290, 129, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(290, 43), (129, 341), (81, 175), (10, 464), (5, 32)]
    (codeMat 206) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane472GenSource0011 :
    QuotientRankAtLeast (spanCodes [290, 129, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(290, 97), (129, 20), (83, 10), (10, 31), (7, 256)]
    (codeMat 110) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane472GenSource0012 :
    QuotientRankAtLeast (spanCodes [290, 130, 71, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(290, 327), (130, 1), (71, 136), (19, 20), (10, 50)]
    (codeMat 205) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane472GenSource0013 :
    QuotientRankAtLeast (spanCodes [290, 128, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(290, 464), (128, 32), (65, 1), (21, 373), (10, 43)]
    (codeMat 317) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane472GenSource0014 :
    QuotientRankAtLeast (spanCodes [290, 130, 67, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(290, 31), (130, 256), (67, 96), (23, 276), (10, 97)]
    (codeMat 335) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane472GenSource0015 :
    QuotientRankAtLeast (spanCodes [290, 144, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(290, 11), (144, 1), (82, 332), (10, 264), (6, 16)]
    (codeMat 142) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane472GenSource0016 :
    QuotientRankAtLeast (spanCodes [290, 145, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(290, 50), (145, 21), (83, 488), (10, 327), (7, 1)]
    (codeMat 241) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane472GenSource0017 :
    QuotientRankAtLeast (spanCodes [290, 129, 66, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(290, 278), (129, 11), (66, 10), (22, 175), (10, 42)]
    (codeMat 397) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane472GenSource0018 :
    QuotientRankAtLeast (spanCodes [279, 149, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(279, 348), (149, 440), (84, 106), (53, 132), (10, 133)]
    (codeMat 115) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane472GenSource0019 :
    QuotientRankAtLeast (spanCodes [277, 151, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(277, 107), (151, 238), (84, 239), (55, 316), (10, 97)]
    (codeMat 285) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

end QiushiMatmul
