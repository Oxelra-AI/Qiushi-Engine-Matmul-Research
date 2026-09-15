import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane467GenFinal
import QiushiPlane468GenFinal
import QiushiPlane473GenFinal
import QiushiPlane475GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0060 :
    QuotientRankAtLeast (spanCodes [298, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [163, 84, 10] [(298, 247), (163, 253), (84, 169)]
    (codeMat 92) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane467Gen_lb18

theorem plane491GenSource0061 :
    QuotientRankAtLeast (spanCodes [299, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(299, 382), (163, 372), (84, 286)]
    (codeMat 244) (codeMat 405) (codeMat 407) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0062 :
    QuotientRankAtLeast (spanCodes [300, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(300, 10), (163, 106), (84, 165)]
    (codeMat 239) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0063 :
    QuotientRankAtLeast (spanCodes [301, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(301, 10), (163, 303), (84, 369)]
    (codeMat 95) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0064 :
    QuotientRankAtLeast (spanCodes [302, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [163, 84, 10] [(302, 84), (163, 163), (84, 94)]
    (codeMat 93) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane467Gen_lb18

theorem plane491GenSource0065 :
    QuotientRankAtLeast (spanCodes [303, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [163, 84, 10] [(303, 163), (163, 94), (84, 247)]
    (codeMat 84) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane467Gen_lb18

theorem plane491GenSource0066 :
    QuotientRankAtLeast (spanCodes [305, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(305, 94), (163, 250), (84, 84)]
    (codeMat 298) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0067 :
    QuotientRankAtLeast (spanCodes [306, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(306, 293), (163, 369), (84, 94)]
    (codeMat 141) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0068 :
    QuotientRankAtLeast (spanCodes [307, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(307, 369), (163, 84), (84, 303)]
    (codeMat 204) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0069 :
    QuotientRankAtLeast (spanCodes [308, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(308, 276), (163, 106), (84, 372)]
    (codeMat 172) (codeMat 250) (codeMat 397) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

end QiushiMatmul
