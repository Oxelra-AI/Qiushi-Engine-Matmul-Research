import QiushiPlane447GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit350From150
import QiushiStep128Mono343From214
import QiushiStep128Mono346From214T
import QiushiStep128Mono348From201
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit202Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane447GenSource0020 :
    QuotientRankAtLeast (spanCodes [266, 152, 56, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(266, 482), (152, 262), (56, 1), (1, 16)]
    (codeMat 266) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane447GenSource0021 :
    QuotientRankAtLeast (spanCodes [264, 134, 38, 28, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(264, 137), (134, 327), (38, 21), (28, 38), (1, 1)]
    (codeMat 281) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane447GenSource0022 :
    QuotientRankAtLeast (spanCodes [270, 134, 38, 26, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(270, 142), (134, 341), (38, 42), (26, 33), (1, 32)]
    (codeMat 395) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane447GenSource0023 :
    QuotientRankAtLeast (spanCodes [268, 158, 62, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(268, 424), (158, 461), (62, 17), (1, 16)]
    (codeMat 267) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane447GenSource0024 :
    QuotientRankAtLeast (spanCodes [306, 160, 70, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 10, 1] [(306, 170), (160, 383), (70, 11), (12, 69), (1, 1)]
    (codeMat 169) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit202_lb16_wc

theorem plane447GenSource0025 :
    QuotientRankAtLeast (spanCodes [306, 160, 66, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 10, 1] [(306, 373), (160, 411), (66, 10), (14, 69), (1, 1)]
    (codeMat 169) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit202_lb16_wc

theorem plane447GenSource0026 :
    QuotientRankAtLeast (spanCodes [294, 160, 68, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(294, 20), (160, 21), (68, 352), (20, 31), (1, 256)]
    (codeMat 117) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane447GenSource0027 :
    QuotientRankAtLeast (spanCodes [306, 160, 82, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 228, 16, 1] [(306, 228), (160, 295), (82, 450), (1, 16)]
    (codeMat 204) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit350_lb16_mono

theorem plane447GenSource0028 :
    QuotientRankAtLeast (spanCodes [306, 160, 84, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(306, 101), (160, 350), (84, 298), (1, 16)]
    (codeMat 205) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane447GenSource0029 :
    QuotientRankAtLeast (spanCodes [294, 160, 66, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(294, 31), (160, 30), (66, 352), (20, 20), (1, 256)]
    (codeMat 93) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
