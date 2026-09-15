import QiushiPlane324GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit168From35T
import QiushiMonoOrbit182From35
import QiushiMonoOrbit198From77T
import QiushiStep128Mono158From72
import QiushiStep128Mono189From80T
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane324GenSource0000 :
    QuotientRankAtLeast (spanCodes [196, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(196, 132), (36, 32), (16, 9), (2, 1), (1, 3)]
    (codeMat 281) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane324GenSource0001 :
    QuotientRankAtLeast (spanCodes [196, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(196, 164), (36, 32), (16, 3), (8, 1), (1, 9)]
    (codeMat 282) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane324GenSource0002 :
    QuotientRankAtLeast (spanCodes [196, 36, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(196, 203), (36, 1), (16, 63), (14, 20), (1, 32)]
    (codeMat 459) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane324GenSource0003 :
    QuotientRankAtLeast (spanCodes [134, 66, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 20, 10, 1] [(134, 20), (66, 11), (36, 260), (16, 128), (1, 1)]
    (codeMat 169) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit168_lb15_mono

theorem plane324GenSource0004 :
    QuotientRankAtLeast (spanCodes [142, 74, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 10, 1] [(142, 117), (74, 11), (36, 325), (16, 32), (1, 1)]
    (codeMat 185) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit182_lb15_mono

theorem plane324GenSource0005 :
    QuotientRankAtLeast (spanCodes [136, 76, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 20, 10, 1] [(136, 11), (76, 272), (36, 260), (16, 1), (1, 128)]
    (codeMat 114) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit168_lb15_mono

theorem plane324GenSource0006 :
    QuotientRankAtLeast (spanCodes [138, 78, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 10, 1] [(138, 11), (78, 304), (36, 325), (16, 1), (1, 32)]
    (codeMat 122) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit182_lb15_mono

theorem plane324GenSource0007 :
    QuotientRankAtLeast (spanCodes [258, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(258, 138), (196, 11), (36, 32), (16, 438), (1, 128)]
    (codeMat 205) (codeMat 242) (codeMat 205) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane324GenSource0008 :
    QuotientRankAtLeast (spanCodes [262, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 132, 32, 10, 1] [(262, 42), (196, 450), (36, 1), (16, 32), (1, 365)]
    (codeMat 171) (codeMat 93) (codeMat 372) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit198_lb15_mono

theorem plane324GenSource0009 :
    QuotientRankAtLeast (spanCodes [264, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(264, 138), (196, 43), (36, 32), (16, 128), (1, 438)]
    (codeMat 214) (codeMat 233) (codeMat 233) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
