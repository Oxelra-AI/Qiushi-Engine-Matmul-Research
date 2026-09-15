import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiBranch262Extraction
import QiushiPlane282GenFinal
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit290Dispatch
import QiushiWcOrbit96Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0000 :
    QuotientRankAtLeast (spanCodes [258, 10, 4, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 12, 2, 1] [(258, 12), (10, 132), (4, 1), (1, 2)]
    (codeMat 161) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit262_lb17

theorem plane425GenSource0001 :
    QuotientRankAtLeast (spanCodes [258, 16, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 264), (16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane425GenSource0002 :
    QuotientRankAtLeast (spanCodes [258, 18, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 280), (18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane425GenSource0003 :
    QuotientRankAtLeast (spanCodes [258, 64, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 12, 2, 1] [(258, 136), (64, 1), (10, 132), (1, 2)]
    (codeMat 140) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit262_lb17

theorem plane425GenSource0004 :
    QuotientRankAtLeast (spanCodes [258, 70, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(258, 43), (70, 10), (10, 79), (1, 1)]
    (codeMat 425) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane425GenSource0005 :
    QuotientRankAtLeast (spanCodes [258, 32, 10, 4, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 8, 2, 1] [(258, 68), (32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit96_lb16_wc

theorem plane425GenSource0006 :
    QuotientRankAtLeast (spanCodes [258, 36, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 112), (36, 1), (20, 62), (10, 20), (1, 32)]
    (codeMat 267) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0007 :
    QuotientRankAtLeast (spanCodes [258, 36, 22, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 80), (36, 1), (22, 10), (10, 52), (1, 32)]
    (codeMat 267) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0008 :
    QuotientRankAtLeast (spanCodes [258, 32, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 80), (32, 1), (20, 10), (10, 20), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0009 :
    QuotientRankAtLeast (spanCodes [258, 32, 22, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 112), (32, 1), (22, 62), (10, 52), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

end QiushiMatmul
