import FrozenRegistry.Btp420Data
import QiushiCertifiedTransport
import FrozenRegistry.UnusedAdapters
import QiushiPlane419GenBindings00
import QiushiPlane487GenBindings08
import QiushiStep126Mono253From96
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane420BtpGenSource0000 :
    QuotientRankAtLeast (spanCodes [68, 8, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 8, 2, 1] [(68, 70), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit253_lb16_mono

theorem plane420BtpGenSource0001 :
    QuotientRankAtLeast (spanCodes [64, 10, 4, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 8, 2, 1] [(64, 8), (10, 70), (4, 3), (1, 1)]
    (codeMat 161) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit253_lb16_mono

theorem plane420BtpGenSource0002 :
    QuotientRankAtLeast (spanCodes [66, 10, 6, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 8, 2, 1] [(66, 70), (10, 78), (6, 3), (1, 1)]
    (codeMat 305) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit253_lb16_mono

theorem plane420BtpGenSource0003 :
    QuotientRankAtLeast (spanCodes [68, 16, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(68, 69), (16, 16), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane487GenBound0081

theorem plane420BtpGenSource0004 :
    QuotientRankAtLeast (spanCodes [68, 18, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(68, 69), (18, 27), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane487GenBound0081

theorem plane420BtpGenSource0005 :
    QuotientRankAtLeast (spanCodes [68, 20, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10, 1] [(68, 69), (20, 21), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.UnusedAdapters.bound284

theorem plane420BtpGenSource0006 :
    QuotientRankAtLeast (spanCodes [68, 22, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10, 1] [(68, 69), (22, 30), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.UnusedAdapters.bound284

theorem plane420BtpGenSource0007 :
    QuotientRankAtLeast (spanCodes [68, 32, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(68, 68), (32, 32), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419GenBound0000

theorem plane420BtpGenSource0008 :
    QuotientRankAtLeast (spanCodes [68, 34, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(68, 69), (34, 43), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419GenBound0000

theorem plane420BtpGenSource0009 :
    QuotientRankAtLeast (spanCodes [68, 36, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(68, 68), (36, 32), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419GenBound0000

end QiushiMatmul
