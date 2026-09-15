import QiushiPlane449GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit311From196
import QiushiMonoOrbit320From196
import QiushiMonoOrbit340From196
import QiushiStep126Mono175From75
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane449GenSource0020 :
    QuotientRankAtLeast (spanCodes [262, 142, 46, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 509), (142, 156), (46, 51), (20, 21), (1, 1)]
    (codeMat 473) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane449GenSource0021 :
    QuotientRankAtLeast (spanCodes [262, 148, 52, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(262, 262), (148, 434), (52, 20), (14, 10), (1, 1)]
    (codeMat 337) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane449GenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 156, 60, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(256, 1), (156, 107), (60, 96), (1, 384)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane449GenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 158, 62, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(258, 274), (158, 359), (62, 17), (1, 16)]
    (codeMat 331) (codeMat 410) (codeMat 331) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane449GenSource0024 :
    QuotientRankAtLeast (spanCodes [316, 160, 66, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 10, 1] [(316, 304), (160, 411), (66, 10), (1, 1)]
    (codeMat 169) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit320_lb16_mono

theorem plane449GenSource0025 :
    QuotientRankAtLeast (spanCodes [316, 160, 78, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 10, 1] [(316, 315), (160, 170), (78, 10), (1, 1)]
    (codeMat 241) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit320_lb16_mono

theorem plane449GenSource0026 :
    QuotientRankAtLeast (spanCodes [316, 160, 80, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(316, 259), (160, 374), (80, 274), (1, 16)]
    (codeMat 143) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane449GenSource0027 :
    QuotientRankAtLeast (spanCodes [300, 160, 66, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(300, 434), (160, 316), (66, 11), (16, 32), (1, 1)]
    (codeMat 169) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane449GenSource0028 :
    QuotientRankAtLeast (spanCodes [298, 160, 68, 22, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(298, 142), (160, 228), (68, 10), (22, 507), (1, 1)]
    (codeMat 425) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane449GenSource0029 :
    QuotientRankAtLeast (spanCodes [316, 160, 84, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(316, 490), (160, 97), (84, 491), (1, 384)]
    (codeMat 302) (codeMat 470) (codeMat 213) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

end QiushiMatmul
