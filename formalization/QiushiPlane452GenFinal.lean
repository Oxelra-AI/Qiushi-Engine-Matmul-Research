import QiushiPlane452GenBool
import QiushiPlane452GenTree
import QiushiPlane452GenDispatch
namespace QiushiMatmul

theorem plane452Gen_lb18 :
    QuotientRankAtLeast (spanCodes [35, 20, 10]) 18 :=
  generic_plane_qra plane452GenConfig plane452GenBool plane452GenSourceQRA plane452GenDeadQRA
    (by decide) plane452GenNoModel

end QiushiMatmul
