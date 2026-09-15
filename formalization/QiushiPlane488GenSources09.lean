import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane295GenFinal
import QiushiPlane315GenFinal
import QiushiPlane433GenFinal
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0090 :
    QuotientRankAtLeast (spanCodes [64, 32, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(64, 16), (32, 1), (10, 258)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane488GenSource0091 :
    QuotientRankAtLeast (spanCodes [66, 34, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(66, 274), (34, 259), (10, 258)]
    (codeMat 114) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane488GenSource0092 :
    QuotientRankAtLeast (spanCodes [131, 96, 18, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(131, 43), (96, 283), (18, 1), (10, 33)]
    (codeMat 187) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane488GenSource0093 :
    QuotientRankAtLeast (spanCodes [160, 96, 16, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(160, 10), (96, 42), (16, 1), (10, 69)]
    (codeMat 98) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane488GenSource0094 :
    QuotientRankAtLeast (spanCodes [165, 96, 18, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(165, 270), (96, 170), (18, 1), (10, 261)]
    (codeMat 115) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane488GenSource0095 :
    QuotientRankAtLeast (spanCodes [180, 96, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(180, 430), (96, 160), (9, 260), (3, 1)]
    (codeMat 177) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane488GenSource0096 :
    QuotientRankAtLeast (spanCodes [257, 96, 10, 5]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(257, 33), (96, 42), (10, 315), (5, 32)]
    (codeMat 117) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane488GenSource0097 :
    QuotientRankAtLeast (spanCodes [260, 96, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(260, 1), (96, 42), (10, 272), (1, 32)]
    (codeMat 85) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane488GenSource0098 :
    QuotientRankAtLeast (spanCodes [259, 96, 10, 4]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(259, 304), (96, 42), (10, 315), (4, 32)]
    (codeMat 103) (codeMat 171) (codeMat 485) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane488GenSource0099 :
    QuotientRankAtLeast (spanCodes [262, 96, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(262, 283), (96, 42), (10, 272), (1, 32)]
    (codeMat 87) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

end QiushiMatmul
