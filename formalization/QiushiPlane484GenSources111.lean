import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1110 :
    QuotientRankAtLeast (spanCodes [257, 65, 32, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 88), (65, 216), (32, 9), (16, 54), (9, 3), (4, 8), (3, 40)]
    (codeMat 267) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1111 :
    QuotientRankAtLeast (spanCodes [320, 32, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(320, 4), (32, 8), (17, 82), (8, 9), (5, 2), (2, 128)]
    (codeMat 266) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane484GenSource1112 :
    QuotientRankAtLeast (spanCodes [257, 64, 32, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 80), (64, 128), (32, 1), (17, 20), (8, 2), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1113 :
    QuotientRankAtLeast (spanCodes [320, 34, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(320, 4), (34, 208), (18, 216), (10, 209), (4, 128), (1, 130)]
    (codeMat 266) (codeMat 465) (codeMat 465) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane484GenSource1114 :
    QuotientRankAtLeast (spanCodes [258, 130, 32, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 88), (130, 216), (32, 9), (18, 3), (10, 60), (4, 8), (1, 32)]
    (codeMat 267) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1115 :
    QuotientRankAtLeast (spanCodes [322, 192, 34, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(322, 120), (192, 128), (34, 60), (18, 63), (10, 61), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1116 :
    QuotientRankAtLeast (spanCodes [384, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(384, 4), (34, 218), (18, 219), (10, 210), (6, 2), (1, 128)]
    (codeMat 266) (codeMat 498) (codeMat 206) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane484GenSource1117 :
    QuotientRankAtLeast (spanCodes [257, 129, 32, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 68), (129, 196), (32, 8), (17, 28), (8, 32), (4, 1), (2, 3)]
    (codeMat 273) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1118 :
    QuotientRankAtLeast (spanCodes [257, 128, 33, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 196), (128, 128), (33, 28), (17, 20), (8, 32), (4, 3), (2, 2)]
    (codeMat 273) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1119 :
    QuotientRankAtLeast (spanCodes [384, 32, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(384, 4), (32, 8), (16, 9), (9, 216), (5, 128), (3, 130)]
    (codeMat 266) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

end QiushiMatmul
