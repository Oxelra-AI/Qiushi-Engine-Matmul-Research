import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiStep132Mono385From243
import QiushiStep133Mono393From243
import QiushiStep133Mono397From243
import QiushiStep133Mono400From243
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0000 :
    QuotientRankAtLeast (spanCodes [160, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(160, 10), (68, 68), (20, 80), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane464GenSource0001 :
    QuotientRankAtLeast (spanCodes [151, 68, 35, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(151, 243), (68, 231), (35, 147), (10, 10)]
    (codeMat 339) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane464GenSource0002 :
    QuotientRankAtLeast (spanCodes [145, 68, 37, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(145, 30), (68, 231), (37, 153), (10, 10)]
    (codeMat 282) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane464GenSource0003 :
    QuotientRankAtLeast (spanCodes [133, 68, 49, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(133, 126), (68, 231), (49, 30), (10, 10)]
    (codeMat 410) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane464GenSource0004 :
    QuotientRankAtLeast (spanCodes [131, 68, 55, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(131, 153), (68, 231), (55, 30), (10, 10)]
    (codeMat 403) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane464GenSource0005 :
    QuotientRankAtLeast (spanCodes [262, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(262, 20), (180, 274), (68, 10), (10, 78)]
    (codeMat 417) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane464GenSource0006 :
    QuotientRankAtLeast (spanCodes [263, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(263, 30), (180, 280), (68, 10), (10, 78)]
    (codeMat 425) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane464GenSource0007 :
    QuotientRankAtLeast (spanCodes [274, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 96, 20, 10] [(274, 265), (180, 96), (68, 126), (10, 259)]
    (codeMat 242) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit400_lb17_mono

theorem plane464GenSource0008 :
    QuotientRankAtLeast (spanCodes [275, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 96, 20, 10] [(275, 116), (180, 30), (68, 126), (10, 259)]
    (codeMat 179) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit400_lb17_mono

theorem plane464GenSource0009 :
    QuotientRankAtLeast (spanCodes [290, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(290, 30), (180, 237), (68, 147), (10, 135)]
    (codeMat 249) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

end QiushiMatmul
