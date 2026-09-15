import QiushiPlane433GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit319From150
import QiushiMonoOrbit340From196
import QiushiMonoOrbit342From196
import QiushiMonoOrbit347From150
import QiushiStep128Mono344From201T
import QiushiStep128Mono346From214T
import QiushiWcOrbit156Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane433GenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 170, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(258, 398), (170, 11), (16, 1), (1, 292)]
    (codeMat 426) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane433GenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 172, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(258, 503), (172, 116), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane433GenSource0022 :
    QuotientRankAtLeast (spanCodes [258, 174, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(258, 440), (174, 116), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane433GenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 138, 74, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 100), (138, 21), (74, 20), (16, 63), (1, 32)]
    (codeMat 124) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane433GenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 198, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [296, 100, 16, 1] [(258, 296), (198, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit342_lb16_mono

theorem plane433GenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 204, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(258, 503), (204, 116), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane433GenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 206, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(258, 440), (206, 116), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane433GenSource0027 :
    QuotientRankAtLeast (spanCodes [258, 224, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(258, 258), (224, 100), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane433GenSource0028 :
    QuotientRankAtLeast (spanCodes [258, 226, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(258, 386), (226, 116), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane433GenSource0029 :
    QuotientRankAtLeast (spanCodes [258, 228, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(258, 258), (228, 228), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

end QiushiMatmul
