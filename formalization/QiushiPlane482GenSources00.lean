import QiushiPlane482GenData
import QiushiCertifiedTransport
import QiushiBranch415Extraction
import QiushiBranch416Extraction
import QiushiMonoOrbit421From279
import QiushiMonoOrbit424From279
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane482GenSource0000 :
    QuotientRankAtLeast (spanCodes [84, 2, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [273, 4, 2] [(84, 273), (2, 4), (1, 2)]
    (codeMat 161) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit415_lb17

theorem plane482GenSource0001 :
    QuotientRankAtLeast (spanCodes [80, 4, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(80, 272), (4, 1), (1, 4)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane482GenSource0002 :
    QuotientRankAtLeast (spanCodes [82, 6, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(82, 272), (6, 1), (1, 4)]
    (codeMat 281) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane482GenSource0003 :
    QuotientRankAtLeast (spanCodes [84, 8, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [273, 4, 2] [(84, 273), (8, 2), (1, 4)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit415_lb17

theorem plane482GenSource0004 :
    QuotientRankAtLeast (spanCodes [84, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 10, 1] [(84, 84), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit421_lb17_mono

theorem plane482GenSource0005 :
    QuotientRankAtLeast (spanCodes [68, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(68, 10), (16, 256), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit424_lb17_mono

theorem plane482GenSource0006 :
    QuotientRankAtLeast (spanCodes [70, 18, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(70, 10), (18, 256), (1, 1)]
    (codeMat 225) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit424_lb17_mono

theorem plane482GenSource0007 :
    QuotientRankAtLeast (spanCodes [64, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(64, 1), (20, 272), (1, 4)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane482GenSource0008 :
    QuotientRankAtLeast (spanCodes [76, 24, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(76, 10), (24, 256), (1, 1)]
    (codeMat 177) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit424_lb17_mono

theorem plane482GenSource0009 :
    QuotientRankAtLeast (spanCodes [66, 22, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(66, 69), (22, 43), (14, 11), (1, 1)]
    (codeMat 273) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

end QiushiMatmul
