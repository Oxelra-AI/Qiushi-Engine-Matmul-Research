import QiushiPlane486GenBool
import QiushiPlane486GenTree
import QiushiPlane486GenDispatch
namespace QiushiMatmul

theorem plane486Gen_lb19 :
    QuotientRankAtLeast (spanCodes [68, 10]) 19 :=
  generic_plane_qra plane486GenConfig plane486GenBool plane486GenSourceQRA plane486GenDeadQRA
    (by decide) plane486GenNoModel

end QiushiMatmul
