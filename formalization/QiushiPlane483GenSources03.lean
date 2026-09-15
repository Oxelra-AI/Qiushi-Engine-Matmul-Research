import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit424From279
import QiushiMonoOrbit440From373
import QiushiMonoOrbit442From373
import QiushiMonoOrbit443From373
import QiushiMonoOrbit444From373
import QiushiPlane282GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0030 :
    QuotientRankAtLeast (spanCodes [160, 114, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(160, 287), (114, 266), (1, 1)]
    (codeMat 185) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0031 :
    QuotientRankAtLeast (spanCodes [160, 118, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(160, 287), (118, 21), (1, 1)]
    (codeMat 409) (codeMat 419) (codeMat 183) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0032 :
    QuotientRankAtLeast (spanCodes [146, 74, 50, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(146, 27), (74, 26), (50, 280), (1, 16)]
    (codeMat 142) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane483GenSource0033 :
    QuotientRankAtLeast (spanCodes [160, 124, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(160, 287), (124, 266), (1, 1)]
    (codeMat 249) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0034 :
    QuotientRankAtLeast (spanCodes [160, 126, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(160, 284), (126, 264), (1, 1)]
    (codeMat 241) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane483GenSource0035 :
    QuotientRankAtLeast (spanCodes [256, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(256, 1), (160, 10), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit424_lb17_mono

theorem plane483GenSource0036 :
    QuotientRankAtLeast (spanCodes [266, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(266, 84), (160, 160), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0037 :
    QuotientRankAtLeast (spanCodes [268, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(268, 20), (160, 224), (1, 1)]
    (codeMat 169) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0038 :
    QuotientRankAtLeast (spanCodes [270, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(270, 85), (160, 245), (1, 1)]
    (codeMat 489) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0039 :
    QuotientRankAtLeast (spanCodes [272, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(272, 10), (160, 11), (1, 256)]
    (codeMat 86) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit424_lb17_mono

end QiushiMatmul
