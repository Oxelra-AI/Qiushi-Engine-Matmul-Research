import QiushiPlane430GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit340From196
import QiushiMonoOrbit342From196
import QiushiStep128Mono343From214
import QiushiStep128Mono344From201T
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane430GenSource0010 :
    QuotientRankAtLeast (spanCodes [266, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(266, 359), (100, 100), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane430GenSource0011 :
    QuotientRankAtLeast (spanCodes [270, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(270, 359), (100, 101), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane430GenSource0012 :
    QuotientRankAtLeast (spanCodes [296, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [296, 100, 16, 1] [(296, 296), (100, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit342_lb16_mono

theorem plane430GenSource0013 :
    QuotientRankAtLeast (spanCodes [298, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(298, 298), (100, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane430GenSource0014 :
    QuotientRankAtLeast (spanCodes [300, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [296, 100, 16, 1] [(300, 296), (100, 101), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit342_lb16_mono

theorem plane430GenSource0015 :
    QuotientRankAtLeast (spanCodes [302, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(302, 298), (100, 101), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane430GenSource0016 :
    QuotientRankAtLeast (spanCodes [386, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(386, 386), (100, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane430GenSource0017 :
    QuotientRankAtLeast (spanCodes [388, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(388, 386), (100, 101), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane430GenSource0018 :
    QuotientRankAtLeast (spanCodes [392, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(392, 503), (100, 100), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane430GenSource0019 :
    QuotientRankAtLeast (spanCodes [398, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(398, 503), (100, 101), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

end QiushiMatmul
