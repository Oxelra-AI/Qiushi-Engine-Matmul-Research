import QiushiPlane254GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit108From29
import QiushiMonoOrbit93From29
import QiushiOrbit101FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane254GenSource0000 :
    QuotientRankAtLeast (spanCodes [68, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 8, 2, 1] [(68, 68), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit93_lb15_mono

theorem plane254GenSource0001 :
    QuotientRankAtLeast (spanCodes [84, 32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(84, 84), (32, 2), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane254GenSource0002 :
    QuotientRankAtLeast (spanCodes [84, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(84, 116), (36, 2), (8, 9), (2, 32), (1, 8)]
    (codeMat 267) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane254GenSource0003 :
    QuotientRankAtLeast (spanCodes [84, 48, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(84, 116), (48, 2), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane254GenSource0004 :
    QuotientRankAtLeast (spanCodes [84, 52, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(84, 84), (52, 34), (8, 9), (2, 32), (1, 8)]
    (codeMat 267) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane254GenSource0005 :
    QuotientRankAtLeast (spanCodes [128, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(128, 2), (84, 84), (8, 32), (2, 1), (1, 8)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane254GenSource0006 :
    QuotientRankAtLeast (spanCodes [132, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(132, 118), (84, 84), (8, 32), (2, 9), (1, 8)]
    (codeMat 177) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane254GenSource0007 :
    QuotientRankAtLeast (spanCodes [144, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(144, 2), (84, 116), (8, 32), (2, 1), (1, 8)]
    (codeMat 177) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane254GenSource0008 :
    QuotientRankAtLeast (spanCodes [148, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(148, 118), (84, 116), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane254GenSource0009 :
    QuotientRankAtLeast (spanCodes [160, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 8, 2, 1] [(160, 160), (84, 84), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit108_lb15_mono

end QiushiMatmul
