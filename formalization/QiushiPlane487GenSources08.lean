import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit431From279
import QiushiPlane315GenFinal
import QiushiPlane429GenFinal
import QiushiPlane439GenFinal
import QiushiStep104Orbit279Split
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0080 :
    QuotientRankAtLeast (spanCodes [84, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [98, 16, 1] [(84, 115), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane429Gen_lb17

theorem plane487GenSource0081 :
    QuotientRankAtLeast (spanCodes [68, 16, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(68, 68), (16, 16), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step104_orbit279_lb17

theorem plane487GenSource0082 :
    QuotientRankAtLeast (spanCodes [70, 18, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [228, 16, 1] [(70, 228), (18, 1), (10, 17)]
    (codeMat 275) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit431_lb17_mono

theorem plane487GenSource0083 :
    QuotientRankAtLeast (spanCodes [70, 18, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(70, 69), (18, 27), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step104_orbit279_lb17

theorem plane487GenSource0084 :
    QuotientRankAtLeast (spanCodes [66, 22, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 20, 1] [(66, 21), (22, 160), (10, 20)]
    (codeMat 142) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane439Gen_lb17

theorem plane487GenSource0085 :
    QuotientRankAtLeast (spanCodes [276, 84, 54, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(276, 160), (84, 161), (54, 260), (10, 430)]
    (codeMat 468) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0086 :
    QuotientRankAtLeast (spanCodes [273, 84, 50, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(273, 270), (84, 271), (50, 170), (10, 430)]
    (codeMat 477) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0087 :
    QuotientRankAtLeast (spanCodes [256, 84, 48, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(256, 1), (84, 271), (48, 260), (10, 430)]
    (codeMat 412) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0088 :
    QuotientRankAtLeast (spanCodes [288, 68, 16, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(288, 260), (68, 160), (16, 1), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0089 :
    QuotientRankAtLeast (spanCodes [260, 84, 53, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(260, 1), (84, 161), (53, 170), (10, 430)]
    (codeMat 405) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
