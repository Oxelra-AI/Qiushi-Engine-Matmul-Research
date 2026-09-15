import QiushiPlane470LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit319From150
import QiushiStep126Mono159From75
import QiushiStep126Mono245From75
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit178Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit235Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470LowerGenSource0030 :
    QuotientRankAtLeast (spanCodes [259, 132, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 10), (132, 20), (68, 21), (16, 256), (10, 352)]
    (codeMat 140) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470LowerGenSource0031 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10, 1] [(259, 21), (129, 11), (64, 1), (20, 240), (10, 80)]
    (codeMat 204) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit159_lb16_mono

theorem plane470LowerGenSource0032 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(259, 42), (130, 32), (64, 1), (20, 315), (10, 101)]
    (codeMat 428) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane470LowerGenSource0033 :
    QuotientRankAtLeast (spanCodes [259, 151, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(259, 293), (151, 160), (84, 161), (10, 399)]
    (codeMat 445) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane470LowerGenSource0034 :
    QuotientRankAtLeast (spanCodes [259, 129, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 161, 68, 20, 10] [(259, 251), (129, 268), (84, 171), (33, 322), (10, 68)]
    (codeMat 234) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit245_lb16_mono

theorem plane470LowerGenSource0035 :
    QuotientRankAtLeast (spanCodes [259, 128, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 508), (128, 1), (84, 156), (33, 373), (10, 463)]
    (codeMat 412) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470LowerGenSource0036 :
    QuotientRankAtLeast (spanCodes [259, 132, 84, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(259, 507), (132, 252), (84, 494), (38, 371), (10, 411)]
    (codeMat 311) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane470LowerGenSource0037 :
    QuotientRankAtLeast (spanCodes [259, 129, 84, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(259, 411), (129, 228), (84, 106), (34, 506), (10, 507)]
    (codeMat 314) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane470LowerGenSource0038 :
    QuotientRankAtLeast (spanCodes [259, 128, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 496), (128, 32), (84, 372), (36, 1), (10, 507)]
    (codeMat 355) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane470LowerGenSource0039 :
    QuotientRankAtLeast (spanCodes [259, 129, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(259, 101), (129, 350), (84, 111), (36, 32), (10, 373)]
    (codeMat 478) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

end QiushiMatmul
