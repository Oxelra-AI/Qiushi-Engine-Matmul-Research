import QiushiPlane448GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit149From65
import QiushiMonoOrbit319From150
import QiushiMonoOrbit347From150
import QiushiMonoOrbit370From196
import QiushiMonoOrbit375From217
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane448GenSource0030 :
    QuotientRankAtLeast (spanCodes [314, 160, 110, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 160, 84, 1] [(314, 382), (160, 479), (110, 394), (1, 1)]
    (codeMat 225) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit375_lb16_mono

theorem plane448GenSource0031 :
    QuotientRankAtLeast (spanCodes [314, 160, 112, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(314, 181), (160, 495), (112, 506), (1, 1)]
    (codeMat 369) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0032 :
    QuotientRankAtLeast (spanCodes [314, 160, 114, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(314, 346), (160, 180), (114, 334), (1, 1)]
    (codeMat 161) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0033 :
    QuotientRankAtLeast (spanCodes [314, 160, 116, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 160, 84, 1] [(314, 161), (160, 479), (116, 394), (1, 1)]
    (codeMat 241) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit375_lb16_mono

theorem plane448GenSource0034 :
    QuotientRankAtLeast (spanCodes [314, 160, 118, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(314, 494), (160, 347), (118, 20), (1, 1)]
    (codeMat 473) (codeMat 421) (codeMat 179) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0035 :
    QuotientRankAtLeast (spanCodes [314, 160, 120, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(314, 302), (160, 389), (120, 388), (1, 292)]
    (codeMat 174) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane448GenSource0036 :
    QuotientRankAtLeast (spanCodes [314, 160, 124, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(314, 181), (160, 347), (124, 335), (1, 1)]
    (codeMat 185) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0037 :
    QuotientRankAtLeast (spanCodes [314, 160, 126, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(314, 275), (160, 245), (126, 258), (1, 16)]
    (codeMat 205) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane448GenSource0038 :
    QuotientRankAtLeast (spanCodes [290, 160, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(290, 376), (160, 104), (16, 8), (8, 1), (1, 2)]
    (codeMat 266) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane448GenSource0039 :
    QuotientRankAtLeast (spanCodes [288, 160, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(288, 27), (160, 11), (16, 1), (10, 68), (1, 256)]
    (codeMat 98) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

end QiushiMatmul
