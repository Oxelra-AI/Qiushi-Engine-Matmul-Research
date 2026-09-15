import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0270 :
    QuotientRankAtLeast (spanCodes [262, 130, 65, 33, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 150), (130, 2), (65, 3), (33, 232), (18, 128), (10, 136)]
    (codeMat 213) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0271 :
    QuotientRankAtLeast (spanCodes [258, 128, 69, 37, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 126), (128, 9), (69, 245), (37, 232), (16, 8), (10, 96)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0272 :
    QuotientRankAtLeast (spanCodes [262, 130, 67, 35, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 148), (130, 2), (67, 20), (35, 252), (16, 3), (10, 28)]
    (codeMat 111) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0273 :
    QuotientRankAtLeast (spanCodes [259, 147, 67, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 105), (147, 30), (67, 235), (35, 96), (10, 232), (4, 8)]
    (codeMat 207) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0274 :
    QuotientRankAtLeast (spanCodes [385, 80, 48, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(385, 22), (80, 255), (48, 3), (9, 9), (5, 130), (3, 128)]
    (codeMat 267) (codeMat 443) (codeMat 254) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0275 :
    QuotientRankAtLeast (spanCodes [276, 128, 65, 33, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(276, 20), (128, 130), (65, 1), (33, 96), (8, 8), (2, 128)]
    (codeMat 85) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0276 :
    QuotientRankAtLeast (spanCodes [385, 80, 48, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(385, 20), (80, 97), (48, 1), (8, 8), (4, 128), (2, 130)]
    (codeMat 266) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0277 :
    QuotientRankAtLeast (spanCodes [276, 134, 68, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(276, 245), (134, 430), (68, 186), (36, 320), (10, 160), (1, 16)]
    (codeMat 206) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane488GenSource0278 :
    QuotientRankAtLeast (spanCodes [386, 82, 50, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(386, 148), (82, 252), (50, 20), (10, 28), (6, 2), (1, 3)]
    (codeMat 401) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0279 :
    QuotientRankAtLeast (spanCodes [258, 176, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 119), (176, 252), (96, 28), (10, 104), (4, 9), (1, 8)]
    (codeMat 185) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
