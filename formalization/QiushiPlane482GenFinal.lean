import QiushiPlane482GenBool
import QiushiPlane482GenTree
import QiushiPlane482GenDispatch
namespace QiushiMatmul

theorem plane482Gen_lb18 :
    QuotientRankAtLeast (spanCodes [84, 1]) 18 :=
  generic_plane_qra plane482GenConfig plane482GenBool plane482GenSourceQRA plane482GenDeadQRA
    (by decide) plane482GenNoModel

end QiushiMatmul
