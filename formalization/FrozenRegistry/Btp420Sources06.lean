import FrozenRegistry.Btp420Data
import QiushiCertifiedTransport
import FrozenRegistry.UnusedAdapters
import QiushiPlane487GenBindings08
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane420BtpGenSource0060 :
    QuotientRankAtLeast (spanCodes [434, 68, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10, 1] [(434, 30), (68, 69), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.UnusedAdapters.bound284

theorem plane420BtpGenSource0061 :
    QuotientRankAtLeast (spanCodes [436, 68, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10, 1] [(436, 21), (68, 69), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.UnusedAdapters.bound284

theorem plane420BtpGenSource0062 :
    QuotientRankAtLeast (spanCodes [438, 68, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(438, 27), (68, 69), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane487GenBound0081

end QiushiMatmul
