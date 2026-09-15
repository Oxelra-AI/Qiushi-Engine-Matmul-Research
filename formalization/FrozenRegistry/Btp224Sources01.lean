import FrozenRegistry.Btp224Data
import QiushiCertifiedTransport
import QiushiPlane269GenBindings01
import QiushiStep99Orbit68Dispatch
import QiushiWcOrbit79Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane224BtpGenSource0010 :
    QuotientRankAtLeast (spanCodes [264, 132, 70, 38, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 164, 68, 16, 10, 1] [(264, 69), (132, 175), (70, 404), (38, 464), (16, 448), (1, 288)]
    (codeMat 158) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit68_lb14_unconditional

theorem plane224BtpGenSource0011 :
    QuotientRankAtLeast (spanCodes [262, 132, 72, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 8, 2, 1] [(262, 493), (132, 338), (72, 32), (40, 1), (16, 2), (1, 256)]
    (codeMat 114) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269GenBound0016

theorem plane224BtpGenSource0012 :
    QuotientRankAtLeast (spanCodes [260, 132, 74, 42, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 160, 96, 20, 10, 1] [(260, 438), (132, 222), (74, 11), (42, 451), (16, 192), (1, 1)]
    (codeMat 177) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit79_lb14_wc

theorem plane224BtpGenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 132, 76, 44, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 164, 68, 16, 10, 1] [(258, 69), (132, 68), (76, 383), (44, 464), (16, 288), (1, 448)]
    (codeMat 93) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit68_lb14_unconditional

theorem plane224BtpGenSource0014 :
    QuotientRankAtLeast (spanCodes [256, 132, 78, 46, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 164, 68, 16, 10, 1] [(256, 1), (132, 79), (78, 180), (46, 240), (16, 448), (1, 288)]
    (codeMat 156) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit68_lb14_unconditional

end QiushiMatmul
