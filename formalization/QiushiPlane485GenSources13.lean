import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit95From31
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0130 :
    QuotientRankAtLeast (spanCodes [262, 192, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(262, 264), (192, 16), (32, 1), (20, 69), (10, 327)]
    (codeMat 98) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane485GenSource0131 :
    QuotientRankAtLeast (spanCodes [258, 197, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 264), (197, 280), (32, 1), (20, 69), (10, 326)]
    (codeMat 106) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane485GenSource0132 :
    QuotientRankAtLeast (spanCodes [32, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 2), (20, 20), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0133 :
    QuotientRankAtLeast (spanCodes [32, 16, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 1), (16, 2), (10, 20), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0134 :
    QuotientRankAtLeast (spanCodes [34, 18, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0135 :
    QuotientRankAtLeast (spanCodes [33, 17, 8, 5, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(33, 30), (17, 28), (8, 3), (5, 40), (2, 32)]
    (codeMat 266) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0136 :
    QuotientRankAtLeast (spanCodes [33, 16, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(33, 60), (16, 2), (9, 63), (4, 32), (3, 40)]
    (codeMat 266) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0137 :
    QuotientRankAtLeast (spanCodes [32, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 2), (17, 62), (9, 63), (5, 40), (3, 8)]
    (codeMat 266) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0138 :
    QuotientRankAtLeast (spanCodes [32, 16, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 1), (16, 2), (9, 54), (4, 8), (3, 32)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0139 :
    QuotientRankAtLeast (spanCodes [32, 17, 8, 5, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 2), (17, 28), (8, 3), (5, 8), (2, 32)]
    (codeMat 266) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

end QiushiMatmul
