import QiushiPlane413GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit271From120
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane413GenSource0030 :
    QuotientRankAtLeast (spanCodes [340, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(340, 337), (32, 32), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0031 :
    QuotientRankAtLeast (spanCodes [344, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(344, 336), (32, 32), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0032 :
    QuotientRankAtLeast (spanCodes [348, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(348, 337), (32, 32), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0033 :
    QuotientRankAtLeast (spanCodes [392, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(392, 336), (32, 32), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0034 :
    QuotientRankAtLeast (spanCodes [396, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(396, 337), (32, 32), (2, 1), (1, 2)]
    (codeMat 337) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0035 :
    QuotientRankAtLeast (spanCodes [408, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(408, 336), (32, 32), (2, 1), (1, 3)]
    (codeMat 273) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0036 :
    QuotientRankAtLeast (spanCodes [412, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(412, 337), (32, 32), (2, 1), (1, 3)]
    (codeMat 337) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0037 :
    QuotientRankAtLeast (spanCodes [456, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(456, 336), (32, 32), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0038 :
    QuotientRankAtLeast (spanCodes [460, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(460, 337), (32, 32), (2, 3), (1, 2)]
    (codeMat 337) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0039 :
    QuotientRankAtLeast (spanCodes [464, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(464, 336), (32, 32), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

end QiushiMatmul
