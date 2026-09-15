import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit431From279
import QiushiMonoOrbit440From373
import QiushiMonoOrbit442From373
import QiushiMonoOrbit443From373
import QiushiPlane282GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0060 :
    QuotientRankAtLeast (spanCodes [342, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(342, 225), (160, 245), (1, 1)]
    (codeMat 249) (codeMat 405) (codeMat 407) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0061 :
    QuotientRankAtLeast (spanCodes [346, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(346, 244), (160, 224), (1, 1)]
    (codeMat 177) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0062 :
    QuotientRankAtLeast (spanCodes [348, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(348, 244), (160, 224), (1, 1)]
    (codeMat 305) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0063 :
    QuotientRankAtLeast (spanCodes [350, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [228, 16, 1] [(350, 245), (160, 228), (1, 16)]
    (codeMat 143) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit431_lb17_mono

theorem plane483GenSource0064 :
    QuotientRankAtLeast (spanCodes [294, 160, 70, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(294, 280), (160, 259), (70, 26), (1, 16)]
    (codeMat 396) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane483GenSource0065 :
    QuotientRankAtLeast (spanCodes [354, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(354, 266), (160, 287), (1, 1)]
    (codeMat 489) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0066 :
    QuotientRankAtLeast (spanCodes [356, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(356, 264), (160, 284), (1, 1)]
    (codeMat 481) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane483GenSource0067 :
    QuotientRankAtLeast (spanCodes [292, 160, 76, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(292, 27), (160, 259), (76, 26), (1, 16)]
    (codeMat 270) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane483GenSource0068 :
    QuotientRankAtLeast (spanCodes [362, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(362, 21), (160, 287), (1, 1)]
    (codeMat 377) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0069 :
    QuotientRankAtLeast (spanCodes [366, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(366, 20), (160, 284), (1, 1)]
    (codeMat 369) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

end QiushiMatmul
