import QiushiPlane456LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit288From150
import QiushiMonoOrbit293From196
import QiushiMonoOrbit342From196
import QiushiMonoOrbit352From196T
import QiushiStep126Mono159From75
import QiushiStep128Mono297From201
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456LowerGenSource0000 :
    QuotientRankAtLeast (spanCodes [161, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(161, 379), (20, 42), (9, 32), (3, 1)]
    (codeMat 281) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane456LowerGenSource0001 :
    QuotientRankAtLeast (spanCodes [161, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(161, 165), (17, 10), (10, 11), (5, 32)]
    (codeMat 459) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane456LowerGenSource0002 :
    QuotientRankAtLeast (spanCodes [161, 19, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [136, 38, 20, 1] [(161, 174), (19, 20), (10, 50), (7, 1)]
    (codeMat 273) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit352_lb16_mono

theorem plane456LowerGenSource0003 :
    QuotientRankAtLeast (spanCodes [128, 33, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [296, 100, 16, 1] [(128, 16), (33, 100), (20, 296), (10, 333)]
    (codeMat 99) (codeMat 345) (codeMat 345) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit342_lb16_mono

theorem plane456LowerGenSource0004 :
    QuotientRankAtLeast (spanCodes [131, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(131, 175), (34, 10), (20, 11), (10, 42)]
    (codeMat 467) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane456LowerGenSource0005 :
    QuotientRankAtLeast (spanCodes [133, 36, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(133, 347), (36, 32), (20, 33), (10, 42)]
    (codeMat 282) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane456LowerGenSource0006 :
    QuotientRankAtLeast (spanCodes [135, 38, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [136, 38, 20, 1] [(135, 136), (38, 38), (20, 50), (10, 21)]
    (codeMat 266) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit352_lb16_mono

theorem plane456LowerGenSource0007 :
    QuotientRankAtLeast (spanCodes [134, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 10, 1] [(134, 276), (39, 30), (20, 20), (10, 31)]
    (codeMat 459) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit288_lb16_mono

theorem plane456LowerGenSource0008 :
    QuotientRankAtLeast (spanCodes [160, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10, 1] [(160, 160), (68, 68), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit159_lb16_mono

theorem plane456LowerGenSource0009 :
    QuotientRankAtLeast (spanCodes [160, 70, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10, 1] [(160, 240), (70, 69), (20, 30), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit159_lb16_mono

end QiushiMatmul
