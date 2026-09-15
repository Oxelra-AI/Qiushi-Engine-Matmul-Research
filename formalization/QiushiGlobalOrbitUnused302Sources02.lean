import QiushiGlobalOrbitUnused302Data
import QiushiCertifiedTransport
import QiushiPlane295GenBindings00
import QiushiStep99Mono3032
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane302UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [304, 180, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(304, 373), (180, 350), (68, 11), (10, 79), (1, 1)]
    (codeMat 481) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295GenBound0001

theorem plane302UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [304, 182, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(304, 315), (182, 283), (68, 10), (10, 79), (1, 1)]
    (codeMat 489) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295GenBound0001

theorem plane302UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [288, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(288, 256), (68, 76), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

theorem plane302UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 64, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(256, 16), (64, 2), (48, 256), (10, 76), (4, 8), (1, 1)]
    (codeMat 161) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

theorem plane302UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [304, 128, 66, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(304, 272), (128, 256), (66, 68), (10, 70), (6, 8), (1, 1)]
    (codeMat 305) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

end QiushiMatmul
