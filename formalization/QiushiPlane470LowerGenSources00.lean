import QiushiPlane470LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit311From196
import QiushiMonoOrbit319From150
import QiushiStep126Mono159From75
import QiushiStep128Mono344From201T
import QiushiStep99Orbit150Dispatch
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit178Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit216Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470LowerGenSource0000 :
    QuotientRankAtLeast (spanCodes [259, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(259, 17), (83, 502), (10, 402), (7, 16)]
    (codeMat 141) (codeMat 214) (codeMat 214) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane470LowerGenSource0001 :
    QuotientRankAtLeast (spanCodes [258, 68, 16, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 258), (68, 68), (16, 16), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane470LowerGenSource0002 :
    QuotientRankAtLeast (spanCodes [259, 67, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(259, 387), (67, 386), (23, 100), (10, 402)]
    (codeMat 124) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane470LowerGenSource0003 :
    QuotientRankAtLeast (spanCodes [259, 80, 33, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10, 1] [(259, 69), (80, 240), (33, 11), (10, 30), (4, 1)]
    (codeMat 273) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit159_lb16_mono

theorem plane470LowerGenSource0004 :
    QuotientRankAtLeast (spanCodes [259, 80, 34, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(259, 79), (80, 373), (34, 11), (10, 43), (4, 1)]
    (codeMat 465) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane470LowerGenSource0005 :
    QuotientRankAtLeast (spanCodes [259, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(259, 160), (84, 171), (39, 388), (10, 389)]
    (codeMat 107) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane470LowerGenSource0006 :
    QuotientRankAtLeast (spanCodes [259, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(259, 490), (84, 395), (48, 384), (10, 480)]
    (codeMat 159) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane470LowerGenSource0007 :
    QuotientRankAtLeast (spanCodes [259, 69, 32, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 301), (69, 164), (32, 32), (17, 10), (10, 11)]
    (codeMat 339) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane470LowerGenSource0008 :
    QuotientRankAtLeast (spanCodes [259, 71, 34, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(259, 418), (71, 238), (34, 451), (19, 133), (10, 450)]
    (codeMat 250) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

theorem plane470LowerGenSource0009 :
    QuotientRankAtLeast (spanCodes [259, 65, 36, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(259, 80), (65, 288), (36, 1), (21, 30), (10, 20)]
    (codeMat 267) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

end QiushiMatmul
