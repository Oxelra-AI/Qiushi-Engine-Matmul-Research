import QiushiPlane465GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane465GenSource0020 :
    QuotientRankAtLeast (spanCodes [293, 163, 68, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(293, 495), (163, 494), (68, 97), (21, 232), (10, 411)]
    (codeMat 317) (codeMat 461) (codeMat 234) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane465GenSource0021 :
    QuotientRankAtLeast (spanCodes [292, 163, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(292, 1), (163, 494), (68, 97), (20, 137), (10, 411)]
    (codeMat 167) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane465GenSource0022 :
    QuotientRankAtLeast (spanCodes [272, 64, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (64, 128), (32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0023 :
    QuotientRankAtLeast (spanCodes [274, 64, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 246), (64, 128), (34, 30), (10, 22), (4, 3), (1, 2)]
    (codeMat 273) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0024 :
    QuotientRankAtLeast (spanCodes [276, 68, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(276, 246), (68, 22), (36, 9), (8, 3), (2, 128), (1, 2)]
    (codeMat 267) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0025 :
    QuotientRankAtLeast (spanCodes [304, 144, 68, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 96), (144, 8), (68, 148), (8, 128), (2, 1), (1, 2)]
    (codeMat 177) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0026 :
    QuotientRankAtLeast (spanCodes [304, 146, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 252), (146, 9), (66, 21), (10, 22), (6, 130), (1, 2)]
    (codeMat 143) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0027 :
    QuotientRankAtLeast (spanCodes [304, 144, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 104), (144, 8), (66, 21), (10, 20), (6, 128), (1, 2)]
    (codeMat 142) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0028 :
    QuotientRankAtLeast (spanCodes [304, 148, 68, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 224), (148, 28), (68, 148), (8, 128), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0029 :
    QuotientRankAtLeast (spanCodes [276, 134, 68, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(276, 245), (134, 430), (68, 186), (36, 320), (10, 160), (1, 16)]
    (codeMat 206) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
