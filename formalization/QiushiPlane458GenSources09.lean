import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0090 :
    QuotientRankAtLeast (spanCodes [261, 164, 97, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 20), (164, 430), (97, 10), (20, 97), (8, 1), (2, 260)]
    (codeMat 106) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0091 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 100), (132, 265), (68, 310), (32, 32), (20, 264), (10, 112)]
    (codeMat 86) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane458GenSource0092 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 192), (131, 10), (65, 1), (34, 272), (20, 160), (10, 20)]
    (codeMat 141) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0093 :
    QuotientRankAtLeast (spanCodes [256, 132, 70, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(256, 32), (132, 264), (70, 344), (34, 100), (20, 265), (10, 91)]
    (codeMat 102) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane458GenSource0094 :
    QuotientRankAtLeast (spanCodes [263, 135, 66, 37, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 31), (135, 283), (66, 223), (37, 464), (20, 170), (10, 367)]
    (codeMat 279) (codeMat 250) (codeMat 397) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0095 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (135, 149), (68, 150), (34, 104), (20, 96), (10, 232)]
    (codeMat 157) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane458GenSource0096 :
    QuotientRankAtLeast (spanCodes [263, 197, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(263, 278), (197, 139), (36, 32), (20, 33), (10, 42)]
    (codeMat 474) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane458GenSource0097 :
    QuotientRankAtLeast (spanCodes [263, 131, 70, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 453), (131, 191), (70, 367), (36, 260), (20, 180), (10, 420)]
    (codeMat 206) (codeMat 351) (codeMat 239) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0098 :
    QuotientRankAtLeast (spanCodes [260, 135, 65, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (135, 150), (65, 130), (39, 224), (20, 255), (10, 227)]
    (codeMat 110) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane458GenSource0099 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (128, 8), (66, 96), (32, 3), (20, 28), (10, 224)]
    (codeMat 116) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
