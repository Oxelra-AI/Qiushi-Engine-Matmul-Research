import QiushiPlane419GenBool
import QiushiPlane419GenTree
import QiushiPlane419GenDispatch
namespace QiushiMatmul

theorem plane419Gen_lb17 :
    QuotientRankAtLeast (spanCodes [32, 10, 1]) 17 :=
  generic_plane_qra plane419GenConfig plane419GenBool plane419GenSourceQRA plane419GenDeadQRA
    (by decide) plane419GenNoModel

end QiushiMatmul
