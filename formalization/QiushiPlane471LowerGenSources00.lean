import QiushiPlane471LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit310From196T
import QiushiStep128Mono346From214T
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit178Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit216Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471LowerGenSource0000 :
    QuotientRankAtLeast (spanCodes [289, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 10, 1] [(289, 10), (80, 304), (10, 96), (4, 1)]
    (codeMat 177) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit310_lb16_mono

theorem plane471LowerGenSource0001 :
    QuotientRankAtLeast (spanCodes [289, 66, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 10, 1] [(289, 10), (66, 97), (22, 304), (10, 96)]
    (codeMat 142) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit310_lb16_mono

theorem plane471LowerGenSource0002 :
    QuotientRankAtLeast (spanCodes [259, 80, 34, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(259, 79), (80, 373), (34, 11), (10, 43), (4, 1)]
    (codeMat 465) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane471LowerGenSource0003 :
    QuotientRankAtLeast (spanCodes [258, 80, 35, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(258, 78), (80, 350), (35, 10), (10, 43), (4, 1)]
    (codeMat 473) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane471LowerGenSource0004 :
    QuotientRankAtLeast (spanCodes [273, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(273, 116), (84, 117), (48, 16), (10, 424)]
    (codeMat 85) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane471LowerGenSource0005 :
    QuotientRankAtLeast (spanCodes [257, 69, 32, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(257, 310), (69, 164), (32, 32), (17, 10), (10, 11)]
    (codeMat 339) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane471LowerGenSource0006 :
    QuotientRankAtLeast (spanCodes [259, 71, 34, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(259, 418), (71, 238), (34, 451), (19, 133), (10, 450)]
    (codeMat 250) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

theorem plane471LowerGenSource0007 :
    QuotientRankAtLeast (spanCodes [261, 65, 36, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(261, 96), (65, 256), (36, 1), (21, 30), (10, 20)]
    (codeMat 331) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane471LowerGenSource0008 :
    QuotientRankAtLeast (spanCodes [260, 64, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(260, 1), (64, 32), (37, 42), (20, 506), (10, 341)]
    (codeMat 285) (codeMat 158) (codeMat 358) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane471LowerGenSource0009 :
    QuotientRankAtLeast (spanCodes [257, 71, 32, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(257, 332), (71, 238), (32, 1), (19, 133), (10, 450)]
    (codeMat 242) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

end QiushiMatmul
