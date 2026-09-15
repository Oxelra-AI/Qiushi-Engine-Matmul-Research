import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane282GenFinal
import QiushiPlane298GenFinal
import QiushiPlane433GenFinal
import QiushiStep128Mono437From262T
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0100 :
    QuotientRankAtLeast (spanCodes [258, 34, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(258, 274), (34, 258), (10, 259)]
    (codeMat 114) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane489GenSource0101 :
    QuotientRankAtLeast (spanCodes [258, 48, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 20, 1] [(258, 20), (48, 1), (10, 100)]
    (codeMat 106) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit437_lb17_mono

theorem plane489GenSource0102 :
    QuotientRankAtLeast (spanCodes [258, 66, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(258, 259), (66, 258), (10, 274)]
    (codeMat 116) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane489GenSource0103 :
    QuotientRankAtLeast (spanCodes [258, 64, 34, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 259), (64, 1), (34, 280), (10, 264)]
    (codeMat 84) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane489GenSource0104 :
    QuotientRankAtLeast (spanCodes [258, 66, 32, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 258), (66, 259), (32, 16), (10, 280)]
    (codeMat 84) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane489GenSource0105 :
    QuotientRankAtLeast (spanCodes [258, 130, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(258, 17), (130, 16), (10, 274)]
    (codeMat 172) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane489GenSource0106 :
    QuotientRankAtLeast (spanCodes [258, 128, 10, 6]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 11), (128, 1), (10, 264), (6, 16)]
    (codeMat 140) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane489GenSource0107 :
    QuotientRankAtLeast (spanCodes [258, 130, 10, 4]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 26), (130, 27), (10, 280), (4, 16)]
    (codeMat 140) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane489GenSource0108 :
    QuotientRankAtLeast (spanCodes [258, 34, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(258, 427), (34, 43), (23, 33), (10, 42)]
    (codeMat 410) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane489GenSource0109 :
    QuotientRankAtLeast (spanCodes [258, 51, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(258, 385), (51, 11), (10, 42), (6, 1)]
    (codeMat 345) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

end QiushiMatmul
