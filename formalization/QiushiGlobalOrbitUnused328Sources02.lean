import QiushiGlobalOrbitUnused328Data
import QiushiCertifiedTransport
import FrozenRegistry.Btp227Final
import QiushiOrbit14FP
import QiushiOrbit29FP
import QiushiPlane315GenBindings00
import QiushiPlane427GenBindings06
import QiushiStep99Orbit67Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane328UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [294, 140, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 140, 96, 16, 1] [(294, 294), (140, 140), (96, 96), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane227BtpGen_lb15

theorem plane328UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [300, 140, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(300, 427), (140, 379), (96, 209), (16, 192), (1, 36)]
    (codeMat 116) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane427GenBound0061

theorem plane328UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [302, 140, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 140, 96, 16, 1] [(302, 458), (140, 140), (96, 96), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane227BtpGen_lb15

theorem plane328UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [132, 96, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(132, 68), (96, 160), (16, 2), (8, 16), (2, 1), (1, 8)]
    (codeMat 273) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane328UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [260, 134, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 16), (134, 170), (96, 420), (16, 320), (10, 69), (1, 260)]
    (codeMat 171) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane328UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [262, 134, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 245), (134, 238), (96, 420), (16, 320), (10, 69), (1, 260)]
    (codeMat 187) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane328UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [290, 134, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 164, 68, 16, 10, 1] [(290, 338), (134, 164), (96, 240), (16, 27), (10, 10), (1, 16)]
    (codeMat 331) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit67_lb15_unconditional

theorem plane328UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [290, 128, 96, 16, 8, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(290, 118), (128, 256), (96, 22), (16, 128), (8, 2), (4, 9), (1, 1)]
    (codeMat 273) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane328UnusedGenSource0028 :
    QuotientRankAtLeast (spanCodes [288, 130, 96, 16, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 511), (130, 256), (96, 151), (16, 128), (8, 2), (6, 9), (1, 1)]
    (codeMat 337) (codeMat 421) (codeMat 179) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
