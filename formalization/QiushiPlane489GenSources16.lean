import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit118From31
import QiushiOrbit31FP
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0160 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(258, 148), (131, 52), (65, 32), (19, 53), (10, 30)]
    (codeMat 358) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane489GenSource0161 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 135), (128, 2), (67, 42), (18, 3), (10, 35)]
    (codeMat 167) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0162 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(258, 168), (129, 47), (65, 45), (18, 32), (10, 35)]
    (codeMat 230) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane489GenSource0163 :
    QuotientRankAtLeast (spanCodes [257, 145, 64, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 132), (145, 41), (64, 2), (9, 3), (3, 32)]
    (codeMat 103) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0164 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 16, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(257, 100), (128, 1), (64, 9), (16, 2), (9, 54), (3, 32)]
    (codeMat 84) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane489GenSource0165 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 100), (128, 9), (64, 8), (18, 54), (10, 52), (1, 32)]
    (codeMat 84) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane489GenSource0166 :
    QuotientRankAtLeast (spanCodes [258, 144, 65, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 269), (144, 32), (65, 390), (48, 1), (10, 294)]
    (codeMat 498) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0167 :
    QuotientRankAtLeast (spanCodes [258, 144, 66, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(258, 166), (144, 2), (66, 139), (48, 32), (10, 136)]
    (codeMat 214) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane489GenSource0168 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 36, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 43), (129, 33), (65, 32), (36, 390), (10, 269)]
    (codeMat 492) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0169 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 36, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 294), (144, 32), (80, 33), (36, 390), (10, 269)]
    (codeMat 500) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
