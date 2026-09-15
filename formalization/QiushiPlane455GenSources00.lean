import QiushiPlane455GenData
import QiushiCertifiedTransport
import QiushiStep132Mono384From243
import QiushiStep132Mono385From243
import QiushiStep133Mono397From243
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane455GenSource0000 :
    QuotientRankAtLeast (spanCodes [129, 20, 8, 2]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(129, 68), (20, 10), (8, 32), (2, 1)]
    (codeMat 273) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane455GenSource0001 :
    QuotientRankAtLeast (spanCodes [129, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(129, 68), (35, 20), (20, 10), (10, 41)]
    (codeMat 337) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane455GenSource0002 :
    QuotientRankAtLeast (spanCodes [129, 37, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(129, 80), (37, 61), (20, 41), (10, 10)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane455GenSource0003 :
    QuotientRankAtLeast (spanCodes [129, 69, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(129, 55), (69, 121), (20, 109), (10, 41)]
    (codeMat 185) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane455GenSource0004 :
    QuotientRankAtLeast (spanCodes [129, 70, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(129, 10), (70, 80), (20, 68), (10, 41)]
    (codeMat 225) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane455GenSource0005 :
    QuotientRankAtLeast (spanCodes [129, 99, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(129, 147), (99, 106), (20, 20), (10, 10)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane455GenSource0006 :
    QuotientRankAtLeast (spanCodes [129, 102, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(129, 20), (102, 249), (20, 147), (10, 10)]
    (codeMat 266) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane455GenSource0007 :
    QuotientRankAtLeast (spanCodes [258, 129, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(258, 20), (129, 10), (20, 160), (10, 80)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane455GenSource0008 :
    QuotientRankAtLeast (spanCodes [289, 129, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(289, 243), (129, 231), (20, 10), (10, 153)]
    (codeMat 275) (codeMat 115) (codeMat 492) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane455GenSource0009 :
    QuotientRankAtLeast (spanCodes [295, 129, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(295, 126), (129, 237), (20, 10), (10, 30)]
    (codeMat 282) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

end QiushiMatmul
