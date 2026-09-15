import QiushiPlane275GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit146Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane275GenSource0010 :
    QuotientRankAtLeast (spanCodes [256, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(256, 32), (160, 264), (84, 84), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane275GenSource0011 :
    QuotientRankAtLeast (spanCodes [260, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(260, 32), (160, 265), (84, 86), (2, 1), (1, 2)]
    (codeMat 169) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane275GenSource0012 :
    QuotientRankAtLeast (spanCodes [264, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(264, 493), (160, 411), (84, 87), (2, 3), (1, 2)]
    (codeMat 185) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane275GenSource0013 :
    QuotientRankAtLeast (spanCodes [268, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(268, 493), (160, 408), (84, 85), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane275GenSource0014 :
    QuotientRankAtLeast (spanCodes [280, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(280, 440), (160, 280), (84, 87), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

theorem plane275GenSource0015 :
    QuotientRankAtLeast (spanCodes [284, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(284, 440), (160, 283), (84, 85), (2, 3), (1, 2)]
    (codeMat 185) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

theorem plane275GenSource0016 :
    QuotientRankAtLeast (spanCodes [296, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(296, 495), (160, 333), (84, 84), (2, 1), (1, 2)]
    (codeMat 225) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

theorem plane275GenSource0017 :
    QuotientRankAtLeast (spanCodes [300, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(300, 495), (160, 332), (84, 86), (2, 1), (1, 2)]
    (codeMat 233) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

theorem plane275GenSource0018 :
    QuotientRankAtLeast (spanCodes [304, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(304, 441), (160, 462), (84, 84), (2, 1), (1, 2)]
    (codeMat 233) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane275GenSource0019 :
    QuotientRankAtLeast (spanCodes [308, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(308, 441), (160, 463), (84, 86), (2, 1), (1, 2)]
    (codeMat 225) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
