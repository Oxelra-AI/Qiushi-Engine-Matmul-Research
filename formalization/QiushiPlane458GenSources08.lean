import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0080 :
    QuotientRankAtLeast (spanCodes [323, 129, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(323, 139), (129, 350), (36, 32), (20, 33), (10, 43)]
    (codeMat 474) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane458GenSource0081 :
    QuotientRankAtLeast (spanCodes [357, 165, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(357, 479), (165, 95), (20, 11), (8, 32), (2, 1)]
    (codeMat 273) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane458GenSource0082 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 42), (132, 21), (68, 20), (20, 376), (10, 264), (1, 32)]
    (codeMat 204) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane458GenSource0083 :
    QuotientRankAtLeast (spanCodes [256, 161, 96, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 1), (161, 213), (96, 11), (20, 96), (9, 192), (3, 432)]
    (codeMat 212) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0084 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 22), (128, 3), (64, 2), (20, 232), (9, 128), (3, 8)]
    (codeMat 204) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane458GenSource0085 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (130, 8), (64, 2), (20, 224), (10, 28), (1, 3)]
    (codeMat 165) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane458GenSource0086 :
    QuotientRankAtLeast (spanCodes [259, 161, 96, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 272), (161, 270), (96, 170), (17, 283), (10, 475), (5, 260)]
    (codeMat 103) (codeMat 123) (codeMat 236) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0087 :
    QuotientRankAtLeast (spanCodes [263, 135, 66, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(263, 170), (135, 284), (66, 138), (20, 413), (10, 139)]
    (codeMat 494) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane458GenSource0088 :
    QuotientRankAtLeast (spanCodes [259, 162, 99, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(259, 283), (162, 138), (99, 494), (18, 1), (10, 261), (6, 128)]
    (codeMat 123) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane458GenSource0089 :
    QuotientRankAtLeast (spanCodes [261, 197, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(261, 43), (197, 42), (20, 316), (8, 438), (2, 32)]
    (codeMat 460) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
