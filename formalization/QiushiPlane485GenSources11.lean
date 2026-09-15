import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane269GenFinal
import QiushiPlane278GenFinal
import QiushiPlane298GenFinal
import QiushiPlane324GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0110 :
    QuotientRankAtLeast (spanCodes [354, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(354, 266), (17, 296), (10, 264), (5, 1)]
    (codeMat 241) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0111 :
    QuotientRankAtLeast (spanCodes [288, 70, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(288, 16), (70, 78), (20, 258), (10, 68), (1, 1)]
    (codeMat 177) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane485GenSource0112 :
    QuotientRankAtLeast (spanCodes [260, 132, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [196, 36, 16, 1] [(260, 36), (132, 52), (20, 53), (10, 197)]
    (codeMat 358) (codeMat 103) (codeMat 188) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane324Gen_lb16

theorem plane485GenSource0113 :
    QuotientRankAtLeast (spanCodes [354, 192, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [196, 36, 16, 1] [(354, 212), (192, 16), (20, 197), (10, 240)]
    (codeMat 423) (codeMat 460) (codeMat 122) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane324Gen_lb16

theorem plane485GenSource0114 :
    QuotientRankAtLeast (spanCodes [256, 192, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(256, 1), (192, 2), (20, 96), (10, 304)]
    (codeMat 84) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0115 :
    QuotientRankAtLeast (spanCodes [320, 128, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(320, 1), (128, 2), (20, 336), (10, 304)]
    (codeMat 92) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0116 :
    QuotientRankAtLeast (spanCodes [384, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(384, 2), (64, 1), (20, 304), (10, 96)]
    (codeMat 140) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0117 :
    QuotientRankAtLeast (spanCodes [448, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(448, 384), (20, 42), (9, 32), (3, 1)]
    (codeMat 281) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane485GenSource0118 :
    QuotientRankAtLeast (spanCodes [260, 195, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(260, 1), (195, 2), (20, 96), (10, 304)]
    (codeMat 85) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0119 :
    QuotientRankAtLeast (spanCodes [325, 130, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(325, 1), (130, 2), (20, 336), (10, 304)]
    (codeMat 93) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
