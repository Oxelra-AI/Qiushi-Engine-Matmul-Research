import QiushiPlane482GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane482GenSource0080 :
    QuotientRankAtLeast (spanCodes [256, 130, 80, 34, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 3), (130, 8), (80, 224), (34, 20), (4, 2), (1, 128)]
    (codeMat 141) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0081 :
    QuotientRankAtLeast (spanCodes [274, 150, 84, 36, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(274, 79), (150, 447), (84, 239), (36, 1), (12, 261), (1, 320)]
    (codeMat 107) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane482GenSource0082 :
    QuotientRankAtLeast (spanCodes [272, 130, 82, 58, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 252), (130, 9), (82, 246), (58, 22), (6, 130), (1, 128)]
    (codeMat 141) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0083 :
    QuotientRankAtLeast (spanCodes [274, 128, 82, 58, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 126), (128, 9), (82, 118), (58, 22), (6, 130), (1, 128)]
    (codeMat 140) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0084 :
    QuotientRankAtLeast (spanCodes [258, 138, 80, 34, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 151), (138, 104), (80, 224), (34, 148), (4, 2), (1, 128)]
    (codeMat 143) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0085 :
    QuotientRankAtLeast (spanCodes [258, 132, 72, 42, 28, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 118), (132, 127), (72, 2), (42, 224), (28, 232), (1, 128)]
    (codeMat 94) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0086 :
    QuotientRankAtLeast (spanCodes [260, 138, 64, 40, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 3), (138, 20), (64, 130), (40, 8), (20, 224), (1, 128)]
    (codeMat 85) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0087 :
    QuotientRankAtLeast (spanCodes [256, 136, 64, 40, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 3), (136, 20), (64, 2), (40, 8), (20, 224), (1, 128)]
    (codeMat 84) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0088 :
    QuotientRankAtLeast (spanCodes [262, 134, 72, 42, 28, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 118), (134, 127), (72, 130), (42, 224), (28, 232), (1, 128)]
    (codeMat 95) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0089 :
    QuotientRankAtLeast (spanCodes [264, 138, 82, 50, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 104), (138, 255), (82, 246), (50, 150), (6, 2), (1, 128)]
    (codeMat 142) (codeMat 498) (codeMat 206) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
