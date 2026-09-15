import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit431From279
import QiushiMonoOrbit440From373
import QiushiMonoOrbit444From373
import QiushiWcOrbit374Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0050 :
    QuotientRankAtLeast (spanCodes [322, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(322, 20), (160, 224), (1, 1)]
    (codeMat 161) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0051 :
    QuotientRankAtLeast (spanCodes [324, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [228, 16, 1] [(324, 17), (160, 228), (1, 16)]
    (codeMat 141) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit431_lb17_mono

theorem plane483GenSource0052 :
    QuotientRankAtLeast (spanCodes [326, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(326, 20), (160, 224), (1, 1)]
    (codeMat 417) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0053 :
    QuotientRankAtLeast (spanCodes [330, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(330, 85), (160, 245), (1, 1)]
    (codeMat 233) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0054 :
    QuotientRankAtLeast (spanCodes [318, 160, 116, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(318, 282), (160, 245), (116, 335), (1, 1)]
    (codeMat 233) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane483GenSource0055 :
    QuotientRankAtLeast (spanCodes [332, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(332, 20), (160, 245), (1, 1)]
    (codeMat 233) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0056 :
    QuotientRankAtLeast (spanCodes [334, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(334, 84), (160, 160), (1, 1)]
    (codeMat 417) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0057 :
    QuotientRankAtLeast (spanCodes [338, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(338, 160), (160, 245), (1, 1)]
    (codeMat 249) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0058 :
    QuotientRankAtLeast (spanCodes [316, 160, 110, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(316, 495), (160, 245), (110, 335), (1, 1)]
    (codeMat 249) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane483GenSource0059 :
    QuotientRankAtLeast (spanCodes [340, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(340, 244), (160, 160), (1, 1)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

end QiushiMatmul
