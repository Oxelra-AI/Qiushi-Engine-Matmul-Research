import QiushiPlane439GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit293From196
import QiushiMonoOrbit310From196T
import QiushiMonoOrbit352From196T
import QiushiStep126Mono159From75
import QiushiStep128Mono297From201
import QiushiWcOrbit178Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane439GenSource0000 :
    QuotientRankAtLeast (spanCodes [160, 20, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(160, 336), (20, 42), (12, 10), (1, 1)]
    (codeMat 273) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane439GenSource0001 :
    QuotientRankAtLeast (spanCodes [160, 20, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 10, 1] [(160, 378), (20, 42), (14, 11), (1, 1)]
    (codeMat 345) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit297_lb16_mono

theorem plane439GenSource0002 :
    QuotientRankAtLeast (spanCodes [136, 40, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(136, 132), (40, 1), (20, 42), (1, 32)]
    (codeMat 266) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane439GenSource0003 :
    QuotientRankAtLeast (spanCodes [138, 42, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(138, 164), (42, 11), (20, 42), (1, 32)]
    (codeMat 331) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane439GenSource0004 :
    QuotientRankAtLeast (spanCodes [142, 46, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [136, 38, 20, 1] [(142, 157), (46, 39), (20, 21), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit352_lb16_mono

theorem plane439GenSource0005 :
    QuotientRankAtLeast (spanCodes [160, 74, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 10, 1] [(160, 304), (74, 10), (20, 96), (1, 1)]
    (codeMat 177) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit310_lb16_mono

theorem plane439GenSource0006 :
    QuotientRankAtLeast (spanCodes [160, 68, 20, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(160, 350), (68, 78), (20, 43), (14, 10), (1, 1)]
    (codeMat 473) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane439GenSource0007 :
    QuotientRankAtLeast (spanCodes [160, 70, 20, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(160, 373), (70, 79), (20, 43), (12, 11), (1, 1)]
    (codeMat 465) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane439GenSource0008 :
    QuotientRankAtLeast (spanCodes [160, 66, 20, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(160, 383), (66, 69), (20, 42), (14, 11), (1, 1)]
    (codeMat 281) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane439GenSource0009 :
    QuotientRankAtLeast (spanCodes [160, 70, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10, 1] [(160, 240), (70, 69), (20, 30), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit159_lb16_mono

end QiushiMatmul
