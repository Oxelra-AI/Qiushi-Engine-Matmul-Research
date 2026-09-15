import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit118From31
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit185Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0100 :
    QuotientRankAtLeast (spanCodes [272, 144, 84, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(272, 416), (144, 32), (84, 94), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane426GenSource0101 :
    QuotientRankAtLeast (spanCodes [272, 128, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (128, 8), (64, 1), (10, 20), (4, 128), (1, 2)]
    (codeMat 140) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0102 :
    QuotientRankAtLeast (spanCodes [272, 130, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 252), (130, 9), (64, 3), (10, 22), (6, 130), (1, 2)]
    (codeMat 141) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0103 :
    QuotientRankAtLeast (spanCodes [272, 130, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 224), (130, 8), (64, 3), (10, 20), (4, 128), (1, 2)]
    (codeMat 141) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0104 :
    QuotientRankAtLeast (spanCodes [272, 128, 68, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (128, 8), (68, 20), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0105 :
    QuotientRankAtLeast (spanCodes [272, 132, 84, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(272, 469), (132, 126), (84, 84), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane426GenSource0106 :
    QuotientRankAtLeast (spanCodes [272, 182, 102, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(272, 495), (182, 42), (102, 485), (10, 126), (1, 432)]
    (codeMat 359) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane426GenSource0107 :
    QuotientRankAtLeast (spanCodes [262, 162, 100, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 464), (162, 170), (100, 202), (22, 191), (10, 283), (1, 192)]
    (codeMat 110) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane426GenSource0108 :
    QuotientRankAtLeast (spanCodes [272, 146, 64, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(272, 166), (146, 45), (64, 2), (10, 15), (1, 1)]
    (codeMat 417) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane426GenSource0109 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 100), (128, 9), (64, 8), (18, 54), (10, 52), (1, 32)]
    (codeMat 84) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

end QiushiMatmul
