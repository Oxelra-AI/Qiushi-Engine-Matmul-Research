import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit322Dispatch
import QiushiWcOrbit374Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0070 :
    QuotientRankAtLeast (spanCodes [306, 160, 66, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 404), (160, 308), (66, 10), (1, 1)]
    (codeMat 481) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane483GenSource0071 :
    QuotientRankAtLeast (spanCodes [284, 160, 110, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(284, 160), (160, 283), (110, 334), (1, 1)]
    (codeMat 169) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane483GenSource0072 :
    QuotientRankAtLeast (spanCodes [298, 160, 92, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(298, 84), (160, 495), (92, 335), (1, 1)]
    (codeMat 241) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane483GenSource0073 :
    QuotientRankAtLeast (spanCodes [306, 160, 74, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 160), (160, 308), (74, 10), (1, 1)]
    (codeMat 369) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane483GenSource0074 :
    QuotientRankAtLeast (spanCodes [270, 160, 116, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(270, 443), (160, 283), (116, 334), (1, 1)]
    (codeMat 185) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane483GenSource0075 :
    QuotientRankAtLeast (spanCodes [298, 160, 86, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(298, 443), (160, 495), (86, 335), (1, 1)]
    (codeMat 225) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane483GenSource0076 :
    QuotientRankAtLeast (spanCodes [134, 38, 18, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(134, 91), (38, 11), (18, 1), (12, 42), (1, 63)]
    (codeMat 275) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane483GenSource0077 :
    QuotientRankAtLeast (spanCodes [262, 160, 18, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(262, 434), (160, 278), (18, 32), (14, 11), (1, 1)]
    (codeMat 473) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane483GenSource0078 :
    QuotientRankAtLeast (spanCodes [258, 160, 22, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 506), (160, 341), (22, 42), (14, 10), (1, 1)]
    (codeMat 465) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane483GenSource0079 :
    QuotientRankAtLeast (spanCodes [258, 140, 44, 22, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 341), (140, 142), (44, 33), (22, 42), (1, 32)]
    (codeMat 459) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
