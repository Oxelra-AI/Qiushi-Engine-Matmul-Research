import QiushiPlane429GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane429GenSource0030 :
    QuotientRankAtLeast (spanCodes [388, 68, 38, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(388, 42), (68, 10), (38, 133), (16, 448), (1, 1)]
    (codeMat 161) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane429GenSource0031 :
    QuotientRankAtLeast (spanCodes [266, 174, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(266, 117), (174, 478), (98, 116), (16, 384), (1, 32)]
    (codeMat 142) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0032 :
    QuotientRankAtLeast (spanCodes [290, 134, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(290, 427), (134, 53), (98, 443), (16, 192), (1, 36)]
    (codeMat 165) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane429GenSource0033 :
    QuotientRankAtLeast (spanCodes [256, 166, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 1), (166, 126), (98, 116), (16, 384), (1, 32)]
    (codeMat 140) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0034 :
    QuotientRankAtLeast (spanCodes [266, 172, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(266, 117), (172, 426), (98, 116), (16, 32), (1, 384)]
    (codeMat 158) (codeMat 340) (codeMat 85) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0035 :
    QuotientRankAtLeast (spanCodes [288, 134, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(288, 16), (134, 209), (98, 443), (16, 192), (1, 36)]
    (codeMat 183) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane429GenSource0036 :
    QuotientRankAtLeast (spanCodes [392, 76, 46, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(392, 356), (76, 10), (46, 132), (16, 448), (1, 1)]
    (codeMat 185) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane429GenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 128, 72, 42, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 118), (128, 9), (72, 2), (42, 96), (16, 8), (1, 128)]
    (codeMat 86) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0038 :
    QuotientRankAtLeast (spanCodes [262, 164, 98, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(262, 368), (164, 197), (98, 181), (16, 27), (10, 10), (1, 16)]
    (codeMat 267) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane429GenSource0039 :
    QuotientRankAtLeast (spanCodes [292, 134, 98, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 27), (134, 480), (98, 491), (16, 260), (10, 69), (1, 320)]
    (codeMat 99) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
