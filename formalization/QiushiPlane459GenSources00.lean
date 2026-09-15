import QiushiPlane459GenData
import QiushiCertifiedTransport
import QiushiStep132Mono385From243
import QiushiWcOrbit300Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane459GenSource0000 :
    QuotientRankAtLeast (spanCodes [160, 68, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 10, 1] [(160, 160), (68, 10), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit300_lb17_wc

theorem plane459GenSource0001 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 10, 1] [(160, 10), (68, 160), (16, 1), (10, 68)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit300_lb17_wc

theorem plane459GenSource0002 :
    QuotientRankAtLeast (spanCodes [160, 68, 17, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 10, 1] [(160, 170), (68, 160), (17, 69), (10, 68)]
    (codeMat 99) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit300_lb17_wc

theorem plane459GenSource0003 :
    QuotientRankAtLeast (spanCodes [160, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(160, 10), (68, 68), (20, 80), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0004 :
    QuotientRankAtLeast (spanCodes [160, 68, 21, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(160, 170), (68, 68), (21, 80), (10, 160)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0005 :
    QuotientRankAtLeast (spanCodes [160, 68, 22, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(160, 10), (68, 228), (22, 80), (10, 160)]
    (codeMat 86) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0006 :
    QuotientRankAtLeast (spanCodes [160, 68, 23, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(160, 170), (68, 228), (23, 80), (10, 160)]
    (codeMat 87) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0007 :
    QuotientRankAtLeast (spanCodes [129, 68, 33, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(129, 20), (68, 10), (33, 80), (10, 160)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0008 :
    QuotientRankAtLeast (spanCodes [131, 68, 35, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(131, 20), (68, 10), (35, 240), (10, 160)]
    (codeMat 141) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0009 :
    QuotientRankAtLeast (spanCodes [133, 68, 37, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(133, 30), (68, 10), (37, 80), (10, 160)]
    (codeMat 204) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

end QiushiMatmul
