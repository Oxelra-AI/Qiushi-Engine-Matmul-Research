import QiushiPlane448GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit319From150
import QiushiMonoOrbit320From196
import QiushiMonoOrbit347From150
import QiushiMonoOrbit370From196
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane448GenSource0000 :
    QuotientRankAtLeast (spanCodes [304, 160, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 10, 1] [(304, 304), (160, 160), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit320_lb16_mono

theorem plane448GenSource0001 :
    QuotientRankAtLeast (spanCodes [280, 130, 34, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(280, 228), (130, 16), (34, 258), (1, 1)]
    (codeMat 169) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane448GenSource0002 :
    QuotientRankAtLeast (spanCodes [286, 132, 36, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(286, 303), (132, 398), (36, 1), (1, 292)]
    (codeMat 491) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane448GenSource0003 :
    QuotientRankAtLeast (spanCodes [284, 134, 38, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(284, 160), (134, 506), (38, 21), (1, 1)]
    (codeMat 465) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0004 :
    QuotientRankAtLeast (spanCodes [274, 136, 40, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(274, 228), (136, 258), (40, 1), (1, 16)]
    (codeMat 266) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane448GenSource0005 :
    QuotientRankAtLeast (spanCodes [274, 132, 36, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(274, 68), (132, 264), (36, 1), (12, 26), (1, 16)]
    (codeMat 267) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane448GenSource0006 :
    QuotientRankAtLeast (spanCodes [272, 138, 42, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(272, 11), (138, 160), (42, 170), (1, 292)]
    (codeMat 342) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane448GenSource0007 :
    QuotientRankAtLeast (spanCodes [276, 142, 46, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(276, 160), (142, 334), (46, 506), (1, 1)]
    (codeMat 377) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0008 :
    QuotientRankAtLeast (spanCodes [264, 146, 50, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(264, 502), (146, 16), (50, 258), (1, 1)]
    (codeMat 185) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane448GenSource0009 :
    QuotientRankAtLeast (spanCodes [270, 148, 52, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(270, 335), (148, 506), (52, 21), (1, 1)]
    (codeMat 337) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

end QiushiMatmul
