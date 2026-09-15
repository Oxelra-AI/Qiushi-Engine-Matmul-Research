import QiushiPlane255GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit110From29
import QiushiMonoOrbit93From29
import QiushiMonoOrbit97From31
import QiushiMonoOrbit98From31T
import QiushiOrbit101FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane255GenSource0000 :
    QuotientRankAtLeast (spanCodes [96, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 8, 2, 1] [(96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit93_lb15_mono

theorem plane255GenSource0001 :
    QuotientRankAtLeast (spanCodes [96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 8, 2, 1] [(96, 96), (20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit97_lb15_mono

theorem plane255GenSource0002 :
    QuotientRankAtLeast (spanCodes [68, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 20, 8, 2, 1] [(68, 20), (36, 8), (8, 3), (2, 128), (1, 2)]
    (codeMat 267) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit98_lb15_mono

theorem plane255GenSource0003 :
    QuotientRankAtLeast (spanCodes [80, 48, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 20, 8, 2, 1] [(80, 20), (48, 128), (8, 2), (2, 8), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit98_lb15_mono

theorem plane255GenSource0004 :
    QuotientRankAtLeast (spanCodes [84, 52, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(84, 84), (52, 34), (8, 9), (2, 32), (1, 8)]
    (codeMat 267) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane255GenSource0005 :
    QuotientRankAtLeast (spanCodes [128, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 32), (96, 132), (8, 2), (2, 8), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane255GenSource0006 :
    QuotientRankAtLeast (spanCodes [132, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 8, 2, 1] [(132, 132), (96, 96), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit110_lb15_mono

theorem plane255GenSource0007 :
    QuotientRankAtLeast (spanCodes [144, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(144, 32), (96, 134), (8, 2), (2, 8), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane255GenSource0008 :
    QuotientRankAtLeast (spanCodes [148, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 8, 2, 1] [(148, 132), (96, 104), (8, 8), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit110_lb15_mono

theorem plane255GenSource0009 :
    QuotientRankAtLeast (spanCodes [160, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(160, 164), (96, 132), (8, 2), (2, 9), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
