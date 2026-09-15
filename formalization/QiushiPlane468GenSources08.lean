import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit183Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0080 :
    QuotientRankAtLeast (spanCodes [258, 162, 67, 17, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 347), (162, 238), (67, 420), (17, 176), (10, 160), (6, 320)]
    (codeMat 94) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0081 :
    QuotientRankAtLeast (spanCodes [262, 164, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 480), (164, 255), (70, 160), (18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0082 :
    QuotientRankAtLeast (spanCodes [276, 164, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(276, 43), (164, 42), (84, 468), (8, 384), (2, 32)]
    (codeMat 94) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane468GenSource0083 :
    QuotientRankAtLeast (spanCodes [276, 164, 84, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(276, 469), (164, 42), (84, 468), (9, 32), (3, 384)]
    (codeMat 92) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane468GenSource0084 :
    QuotientRankAtLeast (spanCodes [260, 164, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 320), (164, 245), (70, 160), (18, 27), (10, 26), (1, 16)]
    (codeMat 330) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0085 :
    QuotientRankAtLeast (spanCodes [258, 134, 84, 34, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(258, 441), (134, 462), (84, 85), (34, 440), (10, 408)]
    (codeMat 214) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane468GenSource0086 :
    QuotientRankAtLeast (spanCodes [288, 164, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(288, 1), (164, 126), (84, 84), (8, 32), (2, 384)]
    (codeMat 86) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane468GenSource0087 :
    QuotientRankAtLeast (spanCodes [258, 130, 84, 38, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(258, 385), (130, 384), (84, 500), (38, 126), (10, 427)]
    (codeMat 372) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane468GenSource0088 :
    QuotientRankAtLeast (spanCodes [260, 132, 84, 32, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(260, 2), (132, 34), (84, 267), (32, 1), (10, 119)]
    (codeMat 298) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane468GenSource0089 :
    QuotientRankAtLeast (spanCodes [261, 133, 84, 33, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(261, 381), (133, 349), (84, 298), (33, 383), (10, 118)]
    (codeMat 167) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

end QiushiMatmul
