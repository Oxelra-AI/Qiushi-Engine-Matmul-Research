import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiStep128Mono158From72
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0180 :
    QuotientRankAtLeast (spanCodes [326, 192, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(326, 33), (192, 32), (33, 245), (20, 222), (10, 235)]
    (codeMat 309) (codeMat 499) (codeMat 382) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane485GenSource0181 :
    QuotientRankAtLeast (spanCodes [354, 192, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(354, 172), (192, 3), (17, 134), (10, 132), (5, 32)]
    (codeMat 95) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0182 :
    QuotientRankAtLeast (spanCodes [323, 195, 34, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(323, 52), (195, 54), (34, 68), (17, 101), (10, 108), (5, 32)]
    (codeMat 99) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0183 :
    QuotientRankAtLeast (spanCodes [386, 34, 18, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(386, 120), (34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0184 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 139), (130, 9), (64, 2), (20, 252), (10, 31), (1, 3)]
    (codeMat 165) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0185 :
    QuotientRankAtLeast (spanCodes [292, 162, 70, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 27), (162, 287), (70, 68), (20, 507), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0186 :
    QuotientRankAtLeast (spanCodes [292, 133, 97, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 260), (133, 26), (97, 261), (20, 160), (8, 320), (2, 16)]
    (codeMat 141) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0187 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 22), (128, 3), (64, 2), (20, 232), (9, 128), (3, 8)]
    (codeMat 204) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0188 :
    QuotientRankAtLeast (spanCodes [260, 161, 101, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 1), (161, 95), (101, 69), (20, 496), (9, 320), (3, 16)]
    (codeMat 205) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0189 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 20), (128, 1), (64, 2), (20, 96), (8, 128), (2, 8)]
    (codeMat 140) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
