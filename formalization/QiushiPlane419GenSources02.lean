import QiushiPlane419GenData
import QiushiCertifiedTransport
import QiushiStep128Mono297From201
import QiushiWcOrbit156Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane419GenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 32, 22, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 112), (32, 1), (22, 62), (10, 52), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 32, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 80), (32, 1), (20, 10), (10, 20), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0022 :
    QuotientRankAtLeast (spanCodes [262, 70, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(262, 112), (70, 79), (32, 32), (10, 68), (1, 1)]
    (codeMat 185) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0023 :
    QuotientRankAtLeast (spanCodes [262, 68, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(262, 80), (68, 11), (32, 32), (10, 68), (1, 1)]
    (codeMat 169) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 70, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 112), (70, 78), (32, 32), (10, 68), (1, 1)]
    (codeMat 177) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 68, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 80), (68, 10), (32, 32), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0026 :
    QuotientRankAtLeast (spanCodes [336, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(336, 336), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane419GenSource0027 :
    QuotientRankAtLeast (spanCodes [338, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(338, 347), (32, 32), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane419GenSource0028 :
    QuotientRankAtLeast (spanCodes [340, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(340, 337), (32, 32), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane419GenSource0029 :
    QuotientRankAtLeast (spanCodes [342, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(342, 346), (32, 32), (10, 11), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

end QiushiMatmul
