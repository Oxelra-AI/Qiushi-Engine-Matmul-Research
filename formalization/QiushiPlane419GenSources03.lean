import QiushiPlane419GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit252From101
import QiushiMonoOrbit299From196
import QiushiMonoOrbit95From31
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane419GenSource0030 :
    QuotientRankAtLeast (spanCodes [386, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(386, 386), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane419GenSource0031 :
    QuotientRankAtLeast (spanCodes [388, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(388, 386), (32, 32), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane419GenSource0032 :
    QuotientRankAtLeast (spanCodes [402, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(402, 418), (32, 32), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane419GenSource0033 :
    QuotientRankAtLeast (spanCodes [404, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(404, 418), (32, 32), (10, 10), (1, 1)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane419GenSource0034 :
    QuotientRankAtLeast (spanCodes [450, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(450, 387), (32, 32), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane419GenSource0035 :
    QuotientRankAtLeast (spanCodes [452, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(452, 386), (32, 32), (10, 11), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane419GenSource0036 :
    QuotientRankAtLeast (spanCodes [464, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(464, 424), (32, 32), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane419GenSource0037 :
    QuotientRankAtLeast (spanCodes [470, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(470, 425), (32, 32), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane419GenSource0038 :
    QuotientRankAtLeast (spanCodes [32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(32, 2), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane419GenSource0039 :
    QuotientRankAtLeast (spanCodes [32, 18, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 2), (18, 54), (10, 53), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

end QiushiMatmul
