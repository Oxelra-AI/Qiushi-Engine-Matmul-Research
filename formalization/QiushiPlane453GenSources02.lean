import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit347From150
import QiushiStep99Orbit150Dispatch
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0020 :
    QuotientRankAtLeast (spanCodes [134, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(134, 100), (68, 69), (20, 91), (10, 10), (1, 1)]
    (codeMat 345) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane453GenSource0021 :
    QuotientRankAtLeast (spanCodes [133, 68, 38, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(133, 137), (68, 475), (38, 50), (20, 38), (10, 21)]
    (codeMat 346) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane453GenSource0022 :
    QuotientRankAtLeast (spanCodes [134, 68, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(134, 508), (68, 475), (37, 338), (20, 509), (10, 21)]
    (codeMat 279) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane453GenSource0023 :
    QuotientRankAtLeast (spanCodes [130, 68, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 32), (68, 475), (37, 383), (20, 464), (10, 42)]
    (codeMat 342) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane453GenSource0024 :
    QuotientRankAtLeast (spanCodes [133, 68, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(133, 164), (68, 475), (34, 10), (20, 11), (10, 42)]
    (codeMat 275) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane453GenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(256, 16), (68, 10), (20, 258), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane453GenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(260, 16), (68, 17), (20, 274), (10, 228)]
    (codeMat 172) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane453GenSource0027 :
    QuotientRankAtLeast (spanCodes [260, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(260, 27), (68, 11), (20, 259), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane453GenSource0028 :
    QuotientRankAtLeast (spanCodes [257, 68, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(257, 96), (68, 352), (32, 1), (20, 10), (10, 21)]
    (codeMat 330) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane453GenSource0029 :
    QuotientRankAtLeast (spanCodes [259, 68, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 373), (68, 30), (34, 352), (20, 96), (10, 353)]
    (codeMat 250) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
