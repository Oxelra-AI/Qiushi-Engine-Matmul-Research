import QiushiGlobalOrbitUnused354Data
import QiushiCertifiedTransport
import QiushiFrozenRank162
import QiushiMonoOrbit124From35T
import QiushiMonoOrbit198From77T
import QiushiPlane292GenBindings00
import QiushiStep128Mono189From80T
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit216Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane354UnusedGenSource0000 :
    QuotientRankAtLeast (spanCodes [128, 96, 20, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(128, 256), (96, 12), (20, 80), (8, 1), (1, 2)]
    (codeMat 266) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane354UnusedGenSource0001 :
    QuotientRankAtLeast (spanCodes [130, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 96, 20, 10, 1] [(130, 128), (96, 97), (20, 20), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRank.span162_lb16

theorem plane354UnusedGenSource0002 :
    QuotientRankAtLeast (spanCodes [136, 66, 34, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(136, 21), (66, 10), (34, 352), (20, 96), (1, 1)]
    (codeMat 225) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane354UnusedGenSource0003 :
    QuotientRankAtLeast (spanCodes [136, 68, 36, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(136, 11), (68, 316), (36, 438), (20, 310), (1, 32)]
    (codeMat 86) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane354UnusedGenSource0004 :
    QuotientRankAtLeast (spanCodes [136, 70, 38, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(136, 43), (70, 316), (38, 164), (20, 310), (1, 32)]
    (codeMat 95) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane354UnusedGenSource0005 :
    QuotientRankAtLeast (spanCodes [136, 76, 44, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 132, 32, 10, 1] [(136, 450), (76, 11), (44, 33), (20, 332), (1, 1)]
    (codeMat 241) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit198_lb15_mono

theorem plane354UnusedGenSource0006 :
    QuotientRankAtLeast (spanCodes [136, 78, 46, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(136, 451), (78, 10), (46, 301), (20, 332), (1, 1)]
    (codeMat 185) (codeMat 419) (codeMat 183) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

theorem plane354UnusedGenSource0007 :
    QuotientRankAtLeast (spanCodes [256, 136, 96, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 96, 20, 10, 1] [(256, 1), (136, 20), (96, 10), (20, 96), (1, 128)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRank.span162_lb16

theorem plane354UnusedGenSource0008 :
    QuotientRankAtLeast (spanCodes [262, 136, 96, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(262, 262), (136, 136), (96, 96), (20, 20), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane354UnusedGenSource0009 :
    QuotientRankAtLeast (spanCodes [264, 136, 96, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 84, 32, 10, 1] [(264, 10), (136, 138), (96, 11), (20, 255), (1, 32)]
    (codeMat 102) (codeMat 190) (codeMat 355) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292GenBound0006

end QiushiMatmul
