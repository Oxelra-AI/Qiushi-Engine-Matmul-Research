import QiushiPlane457GenData
import QiushiCertifiedTransport
import QiushiStep132Mono384From243
import QiushiStep133Mono393From243
import QiushiStep133Mono397From243
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane457GenSource0000 :
    QuotientRankAtLeast (spanCodes [449, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(449, 68), (35, 55), (20, 30), (10, 35)]
    (codeMat 273) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane457GenSource0001 :
    QuotientRankAtLeast (spanCodes [449, 37, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(449, 68), (37, 20), (20, 61), (10, 35)]
    (codeMat 281) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane457GenSource0002 :
    QuotientRankAtLeast (spanCodes [389, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(389, 68), (68, 322), (20, 280), (10, 80)]
    (codeMat 93) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane457GenSource0003 :
    QuotientRankAtLeast (spanCodes [388, 69, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(388, 68), (69, 322), (20, 328), (10, 80)]
    (codeMat 85) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane457GenSource0004 :
    QuotientRankAtLeast (spanCodes [417, 96, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(417, 249), (96, 135), (20, 237), (10, 243)]
    (codeMat 501) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane457GenSource0005 :
    QuotientRankAtLeast (spanCodes [422, 103, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(422, 10), (103, 116), (20, 30), (10, 243)]
    (codeMat 445) (codeMat 85) (codeMat 340) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane457GenSource0006 :
    QuotientRankAtLeast (spanCodes [322, 131, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(322, 153), (131, 10), (20, 237), (10, 30)]
    (codeMat 485) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane457GenSource0007 :
    QuotientRankAtLeast (spanCodes [326, 135, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(326, 10), (135, 20), (20, 280), (10, 328)]
    (codeMat 205) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane457GenSource0008 :
    QuotientRankAtLeast (spanCodes [353, 160, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(353, 322), (160, 268), (20, 328), (10, 280)]
    (codeMat 213) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane457GenSource0009 :
    QuotientRankAtLeast (spanCodes [355, 162, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(355, 106), (162, 10), (20, 30), (10, 237)]
    (codeMat 317) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

end QiushiMatmul
