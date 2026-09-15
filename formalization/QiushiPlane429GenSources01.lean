import QiushiPlane429GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane429GenSource0010 :
    QuotientRankAtLeast (spanCodes [136, 68, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(136, 28), (68, 96), (36, 128), (16, 3), (2, 1), (1, 8)]
    (codeMat 281) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0011 :
    QuotientRankAtLeast (spanCodes [260, 98, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(260, 384), (98, 117), (16, 32), (14, 10), (1, 1)]
    (codeMat 337) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0012 :
    QuotientRankAtLeast (spanCodes [256, 98, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 384), (98, 116), (16, 32), (14, 10), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0013 :
    QuotientRankAtLeast (spanCodes [264, 66, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 20), (66, 96), (32, 2), (16, 128), (4, 1), (1, 8)]
    (codeMat 273) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0014 :
    QuotientRankAtLeast (spanCodes [258, 74, 40, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (74, 118), (40, 2), (16, 128), (4, 8), (1, 9)]
    (codeMat 273) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0015 :
    QuotientRankAtLeast (spanCodes [266, 138, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(266, 394), (138, 10), (98, 117), (16, 1), (1, 32)]
    (codeMat 106) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0016 :
    QuotientRankAtLeast (spanCodes [294, 166, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(294, 43), (166, 42), (98, 84), (16, 32), (1, 384)]
    (codeMat 156) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0017 :
    QuotientRankAtLeast (spanCodes [292, 160, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(292, 448), (160, 490), (98, 459), (16, 325), (1, 32)]
    (codeMat 461) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane429GenSource0018 :
    QuotientRankAtLeast (spanCodes [270, 136, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(270, 394), (136, 10), (98, 85), (16, 1), (1, 32)]
    (codeMat 98) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0019 :
    QuotientRankAtLeast (spanCodes [290, 164, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(290, 43), (164, 42), (98, 468), (16, 32), (1, 384)]
    (codeMat 157) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

end QiushiMatmul
