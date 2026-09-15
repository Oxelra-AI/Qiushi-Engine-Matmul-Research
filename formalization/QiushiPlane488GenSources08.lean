import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane295GenFinal
import QiushiPlane430GenFinal
import QiushiPlane458GenFinal
import QiushiPlane466GenFinal
import QiushiPlane471GenFinal
import QiushiPlane474GenFinal
import QiushiPlane475GenFinal
import QiushiStep104Orbit279Split
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0080 :
    QuotientRankAtLeast (spanCodes [433, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(433, 96), (96, 175), (10, 197)]
    (codeMat 123) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane488GenSource0081 :
    QuotientRankAtLeast (spanCodes [434, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(434, 456), (96, 20), (10, 450)]
    (codeMat 114) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane488GenSource0082 :
    QuotientRankAtLeast (spanCodes [435, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(435, 300), (96, 376), (10, 294)]
    (codeMat 307) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane488GenSource0083 :
    QuotientRankAtLeast (spanCodes [436, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(436, 10), (96, 289), (10, 383)]
    (codeMat 254) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane488GenSource0084 :
    QuotientRankAtLeast (spanCodes [437, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(437, 68), (96, 78), (10, 383)]
    (codeMat 110) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane488GenSource0085 :
    QuotientRankAtLeast (spanCodes [439, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(439, 294), (96, 10), (10, 376)]
    (codeMat 214) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane488GenSource0086 :
    QuotientRankAtLeast (spanCodes [96, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(96, 100), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane488GenSource0087 :
    QuotientRankAtLeast (spanCodes [96, 18, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(96, 100), (18, 16), (10, 17)]
    (codeMat 282) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane488GenSource0088 :
    QuotientRankAtLeast (spanCodes [96, 17, 8, 2]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(96, 68), (17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step104_orbit279_lb17

theorem plane488GenSource0089 :
    QuotientRankAtLeast (spanCodes [96, 20, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(96, 315), (20, 42), (9, 32), (3, 1)]
    (codeMat 345) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

end QiushiMatmul
