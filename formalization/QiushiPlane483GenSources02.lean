import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit440From373
import QiushiMonoOrbit442From373
import QiushiMonoOrbit443From373
import QiushiMonoOrbit444From373
import QiushiPlane282GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0020 :
    QuotientRankAtLeast (spanCodes [160, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(160, 160), (84, 84), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0021 :
    QuotientRankAtLeast (spanCodes [160, 86, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(160, 245), (86, 85), (1, 1)]
    (codeMat 473) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0022 :
    QuotientRankAtLeast (spanCodes [160, 90, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(160, 245), (90, 20), (1, 1)]
    (codeMat 345) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0023 :
    QuotientRankAtLeast (spanCodes [160, 92, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(160, 245), (92, 85), (1, 1)]
    (codeMat 345) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0024 :
    QuotientRankAtLeast (spanCodes [160, 94, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(160, 160), (94, 84), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0025 :
    QuotientRankAtLeast (spanCodes [130, 66, 34, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(130, 27), (66, 26), (34, 280), (1, 16)]
    (codeMat 140) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane483GenSource0026 :
    QuotientRankAtLeast (spanCodes [160, 100, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(160, 284), (100, 264), (1, 1)]
    (codeMat 225) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane483GenSource0027 :
    QuotientRankAtLeast (spanCodes [160, 102, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(160, 287), (102, 266), (1, 1)]
    (codeMat 233) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0028 :
    QuotientRankAtLeast (spanCodes [160, 106, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(160, 287), (106, 266), (1, 1)]
    (codeMat 169) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0029 :
    QuotientRankAtLeast (spanCodes [160, 108, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(160, 287), (108, 21), (1, 1)]
    (codeMat 281) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

end QiushiMatmul
