import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiStep132Mono384From243
import QiushiStep132Mono385From243
import QiushiStep133Mono393From243
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0000 :
    QuotientRankAtLeast (spanCodes [68, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(68, 68), (35, 35), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane453GenSource0001 :
    QuotientRankAtLeast (spanCodes [68, 37, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(68, 68), (37, 41), (20, 30), (10, 10)]
    (codeMat 345) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane453GenSource0002 :
    QuotientRankAtLeast (spanCodes [131, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(131, 55), (68, 121), (20, 109), (10, 41)]
    (codeMat 177) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane453GenSource0003 :
    QuotientRankAtLeast (spanCodes [133, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(133, 78), (68, 121), (20, 68), (10, 41)]
    (codeMat 241) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane453GenSource0004 :
    QuotientRankAtLeast (spanCodes [160, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(160, 10), (68, 68), (20, 80), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane453GenSource0005 :
    QuotientRankAtLeast (spanCodes [262, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(262, 262), (68, 68), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane453GenSource0006 :
    QuotientRankAtLeast (spanCodes [263, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(263, 322), (68, 68), (20, 30), (10, 10)]
    (codeMat 345) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane453GenSource0007 :
    QuotientRankAtLeast (spanCodes [290, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(290, 80), (68, 268), (20, 10), (10, 20)]
    (codeMat 394) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane453GenSource0008 :
    QuotientRankAtLeast (spanCodes [293, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(293, 328), (68, 268), (20, 30), (10, 20)]
    (codeMat 395) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane453GenSource0009 :
    QuotientRankAtLeast (spanCodes [386, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(386, 68), (68, 322), (20, 328), (10, 80)]
    (codeMat 84) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

end QiushiMatmul
