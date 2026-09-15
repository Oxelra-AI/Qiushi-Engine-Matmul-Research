import QiushiPlane413GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit252From101
import QiushiMonoOrbit259From120
import QiushiStep128Mono266From98T
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane413GenSource0010 :
    QuotientRankAtLeast (spanCodes [32, 24, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(32, 2), (24, 1), (2, 32), (1, 40)]
    (codeMat 266) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane413GenSource0011 :
    QuotientRankAtLeast (spanCodes [32, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 12, 2, 1] [(32, 32), (28, 12), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit259_lb15_mono

theorem plane413GenSource0012 :
    QuotientRankAtLeast (spanCodes [80, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [80, 32, 2, 1] [(80, 80), (32, 32), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit266_lb15_mono

theorem plane413GenSource0013 :
    QuotientRankAtLeast (spanCodes [68, 32, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(68, 132), (32, 32), (16, 8), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane413GenSource0014 :
    QuotientRankAtLeast (spanCodes [88, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [80, 32, 2, 1] [(88, 80), (32, 32), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit266_lb15_mono

theorem plane413GenSource0015 :
    QuotientRankAtLeast (spanCodes [68, 32, 24, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(68, 132), (32, 32), (24, 8), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane413GenSource0016 :
    QuotientRankAtLeast (spanCodes [136, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [80, 32, 2, 1] [(136, 80), (32, 32), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit266_lb15_mono

theorem plane413GenSource0017 :
    QuotientRankAtLeast (spanCodes [132, 32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(132, 132), (32, 32), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane413GenSource0018 :
    QuotientRankAtLeast (spanCodes [152, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [80, 32, 2, 1] [(152, 80), (32, 32), (2, 1), (1, 3)]
    (codeMat 273) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit266_lb15_mono

theorem plane413GenSource0019 :
    QuotientRankAtLeast (spanCodes [132, 32, 24, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(132, 132), (32, 32), (24, 8), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
