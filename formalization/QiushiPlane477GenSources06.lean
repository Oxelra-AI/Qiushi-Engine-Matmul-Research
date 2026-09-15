import QiushiPlane477GenData
import QiushiCertifiedTransport
import QiushiWcOrbit374Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane477GenSource0060 :
    QuotientRankAtLeast (spanCodes [286, 158, 84, 61]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(286, 443), (158, 442), (84, 85), (61, 160)]
    (codeMat 92) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane477GenSource0061 :
    QuotientRankAtLeast (spanCodes [286, 157, 84, 62]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(286, 282), (157, 442), (84, 85), (62, 283)]
    (codeMat 102) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane477GenSource0062 :
    QuotientRankAtLeast (spanCodes [286, 156, 84, 63]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(286, 161), (156, 442), (84, 85), (63, 1)]
    (codeMat 115) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

end QiushiMatmul
