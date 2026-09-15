import FrozenRegistry.Btp285Data
import QiushiCertifiedTransport
import QiushiFrozenRank162
import QiushiOrbit35FP
import QiushiPlane315GenBindings01
import QiushiWcOrbit164Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane285BtpGenSource0010 :
    QuotientRankAtLeast (spanCodes [130, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 96, 20, 10, 1] [(130, 128), (96, 97), (20, 20), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRank.span162_lb16

theorem plane285BtpGenSource0011 :
    QuotientRankAtLeast (spanCodes [132, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 96, 20, 10, 1] [(132, 149), (96, 96), (20, 21), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRank.span162_lb16

theorem plane285BtpGenSource0012 :
    QuotientRankAtLeast (spanCodes [134, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 96, 20, 10, 1] [(134, 148), (96, 126), (20, 20), (10, 11), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRank.span162_lb16

theorem plane285BtpGenSource0013 :
    QuotientRankAtLeast (spanCodes [160, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(160, 232), (96, 104), (20, 29), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane285BtpGenSource0014 :
    QuotientRankAtLeast (spanCodes [160, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(160, 160), (96, 96), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0017

theorem plane285BtpGenSource0015 :
    QuotientRankAtLeast (spanCodes [162, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(162, 160), (96, 97), (20, 20), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0017

theorem plane285BtpGenSource0016 :
    QuotientRankAtLeast (spanCodes [164, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(164, 245), (96, 96), (20, 29), (8, 8), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane285BtpGenSource0017 :
    QuotientRankAtLeast (spanCodes [164, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(164, 160), (96, 126), (20, 20), (10, 11), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0017

theorem plane285BtpGenSource0018 :
    QuotientRankAtLeast (spanCodes [166, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(166, 191), (96, 96), (20, 21), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0017

theorem plane285BtpGenSource0019 :
    QuotientRankAtLeast (spanCodes [256, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(256, 256), (96, 96), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
