import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0390 :
    QuotientRankAtLeast (spanCodes [271, 135, 65, 36, 21]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(271, 279), (135, 43), (65, 438), (36, 128), (21, 42)]
    (codeMat 415) (codeMat 331) (codeMat 410) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane491GenSource0391 :
    QuotientRankAtLeast (spanCodes [259, 135, 67, 36, 23, 14]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(259, 316), (135, 333), (67, 81), (36, 63), (23, 332), (14, 278)]
    (codeMat 494) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane491GenSource0392 :
    QuotientRankAtLeast (spanCodes [259, 130, 70, 33, 18, 14]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 104), (130, 1), (70, 97), (33, 252), (18, 3), (14, 227)]
    (codeMat 117) (codeMat 355) (codeMat 190) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0393 :
    QuotientRankAtLeast (spanCodes [262, 134, 71, 37, 19, 14]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 126), (134, 119), (71, 139), (37, 232), (19, 224), (14, 136)]
    (codeMat 159) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0394 :
    QuotientRankAtLeast (spanCodes [263, 135, 70, 36, 18, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 224), (135, 227), (70, 31), (36, 128), (18, 130), (15, 22)]
    (codeMat 95) (codeMat 395) (codeMat 474) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0395 :
    QuotientRankAtLeast (spanCodes [263, 134, 71, 37, 19, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(263, 90), (134, 278), (71, 101), (37, 376), (19, 344), (15, 264)]
    (codeMat 159) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane491GenSource0396 :
    QuotientRankAtLeast (spanCodes [257, 130, 70, 33, 18, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 224), (130, 3), (70, 252), (33, 96), (18, 1), (12, 104)]
    (codeMat 115) (codeMat 330) (codeMat 394) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0397 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 39, 16, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 363), (132, 436), (68, 437), (39, 463), (16, 16), (12, 430)]
    (codeMat 468) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0398 :
    QuotientRankAtLeast (spanCodes [258, 129, 64, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 436), (129, 78), (64, 1), (34, 176), (20, 160), (10, 496)]
    (codeMat 156) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0399 :
    QuotientRankAtLeast (spanCodes [258, 134, 69, 37, 17, 8]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 222), (134, 437), (69, 436), (37, 272), (17, 96), (8, 256)]
    (codeMat 157) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
