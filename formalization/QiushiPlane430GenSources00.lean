import QiushiPlane430GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit340From196
import QiushiStep128Mono297From201
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit178Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane430GenSource0000 :
    QuotientRankAtLeast (spanCodes [66, 38, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(66, 68), (38, 31), (16, 32), (12, 11), (1, 1)]
    (codeMat 273) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane430GenSource0001 :
    QuotientRankAtLeast (spanCodes [70, 34, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(70, 69), (34, 21), (16, 63), (12, 11), (1, 1)]
    (codeMat 281) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane430GenSource0002 :
    QuotientRankAtLeast (spanCodes [136, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(136, 10), (100, 336), (16, 1), (1, 32)]
    (codeMat 98) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane430GenSource0003 :
    QuotientRankAtLeast (spanCodes [138, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(138, 10), (100, 368), (16, 1), (1, 32)]
    (codeMat 106) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane430GenSource0004 :
    QuotientRankAtLeast (spanCodes [138, 78, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(138, 69), (78, 272), (42, 11), (16, 1), (1, 32)]
    (codeMat 458) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane430GenSource0005 :
    QuotientRankAtLeast (spanCodes [136, 78, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(136, 69), (78, 304), (42, 11), (16, 1), (1, 32)]
    (codeMat 394) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane430GenSource0006 :
    QuotientRankAtLeast (spanCodes [138, 70, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(138, 68), (70, 304), (34, 11), (16, 1), (1, 32)]
    (codeMat 330) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane430GenSource0007 :
    QuotientRankAtLeast (spanCodes [136, 70, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(136, 68), (70, 272), (34, 11), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane430GenSource0008 :
    QuotientRankAtLeast (spanCodes [258, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(258, 258), (100, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane430GenSource0009 :
    QuotientRankAtLeast (spanCodes [262, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(262, 258), (100, 101), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

end QiushiMatmul
