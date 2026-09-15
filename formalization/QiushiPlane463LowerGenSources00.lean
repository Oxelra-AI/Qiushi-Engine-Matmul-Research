import QiushiPlane463LowerGenData
import QiushiCertifiedTransport
import QiushiStep126Mono159From75
import QiushiWcOrbit147Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit334Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463LowerGenSource0000 :
    QuotientRankAtLeast (spanCodes [162, 68, 16, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 16, 10, 1] [(162, 78), (68, 176), (16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit147_lb16_wc

theorem plane463LowerGenSource0001 :
    QuotientRankAtLeast (spanCodes [161, 68, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [140, 98, 16, 1] [(161, 99), (68, 255), (18, 1), (10, 17)]
    (codeMat 275) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit334_lb16_wc

theorem plane463LowerGenSource0002 :
    QuotientRankAtLeast (spanCodes [166, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10, 1] [(166, 228), (68, 79), (20, 31), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit159_lb16_mono

theorem plane463LowerGenSource0003 :
    QuotientRankAtLeast (spanCodes [164, 68, 22, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10, 1] [(164, 228), (68, 68), (22, 31), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit159_lb16_mono

theorem plane463LowerGenSource0004 :
    QuotientRankAtLeast (spanCodes [131, 68, 36, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(131, 383), (68, 475), (36, 32), (20, 33), (10, 42)]
    (codeMat 346) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0005 :
    QuotientRankAtLeast (spanCodes [131, 68, 39, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(131, 175), (68, 497), (39, 43), (23, 11), (10, 42)]
    (codeMat 467) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0006 :
    QuotientRankAtLeast (spanCodes [130, 68, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 32), (68, 475), (37, 383), (20, 464), (10, 42)]
    (codeMat 342) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0007 :
    QuotientRankAtLeast (spanCodes [130, 68, 38, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 1), (68, 497), (38, 133), (23, 506), (10, 42)]
    (codeMat 477) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0008 :
    QuotientRankAtLeast (spanCodes [129, 68, 36, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(129, 175), (68, 497), (36, 1), (22, 11), (10, 42)]
    (codeMat 403) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0009 :
    QuotientRankAtLeast (spanCodes [128, 68, 37, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(128, 1), (68, 497), (37, 175), (22, 506), (10, 42)]
    (codeMat 412) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
