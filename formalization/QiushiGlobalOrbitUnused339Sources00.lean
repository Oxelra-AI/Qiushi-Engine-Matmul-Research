import QiushiGlobalOrbitUnused339Data
import QiushiCertifiedTransport
import QiushiMonoOrbit130From35T
import QiushiMonoOrbit134From35T
import QiushiMonoOrbit182From35
import QiushiPlane267GenBindings00
import QiushiPlane298GenBindings00
import QiushiStep98Orbit153Mono
import QiushiWcOrbit165Dispatch
import QiushiWcOrbit180Dispatch
import QiushiWcOrbit185Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane339UnusedGenSource0000 :
    QuotientRankAtLeast (spanCodes [296, 98, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(296, 80), (98, 204), (16, 32), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane339UnusedGenSource0001 :
    QuotientRankAtLeast (spanCodes [296, 98, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(296, 440), (98, 116), (16, 32), (6, 2), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267GenBound0009

theorem plane339UnusedGenSource0002 :
    QuotientRankAtLeast (spanCodes [290, 98, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 10, 1] [(290, 362), (98, 106), (16, 16), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step98_orbit153_lb15_unconditional

theorem plane339UnusedGenSource0003 :
    QuotientRankAtLeast (spanCodes [292, 98, 16, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [144, 84, 32, 10, 1] [(292, 144), (98, 85), (16, 32), (12, 10), (1, 1)]
    (codeMat 337) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit180_lb15_wc

theorem plane339UnusedGenSource0004 :
    QuotientRankAtLeast (spanCodes [294, 98, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(294, 452), (98, 117), (16, 32), (14, 11), (1, 1)]
    (codeMat 465) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane339UnusedGenSource0005 :
    QuotientRankAtLeast (spanCodes [264, 66, 32, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(264, 12), (66, 160), (32, 1), (16, 2), (1, 256)]
    (codeMat 98) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane339UnusedGenSource0006 :
    QuotientRankAtLeast (spanCodes [268, 70, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 10, 1] [(268, 42), (70, 304), (36, 1), (16, 325), (1, 32)]
    (codeMat 107) (codeMat 142) (codeMat 354) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit182_lb15_mono

theorem plane339UnusedGenSource0007 :
    QuotientRankAtLeast (spanCodes [270, 68, 38, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(270, 84), (68, 10), (38, 127), (16, 384), (1, 1)]
    (codeMat 489) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298GenBound0004

theorem plane339UnusedGenSource0008 :
    QuotientRankAtLeast (spanCodes [258, 72, 42, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(258, 173), (72, 1), (42, 160), (16, 256), (1, 2)]
    (codeMat 142) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane339UnusedGenSource0009 :
    QuotientRankAtLeast (spanCodes [262, 76, 46, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(262, 127), (76, 10), (46, 97), (16, 320), (1, 1)]
    (codeMat 249) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

end QiushiMatmul
