import QiushiPlane457GenBool
import QiushiPlane457GenTree
import QiushiPlane457GenDispatch
namespace QiushiMatmul

theorem plane457Gen_lb18 :
    QuotientRankAtLeast (spanCodes [449, 20, 10]) 18 :=
  generic_plane_qra plane457GenConfig plane457GenBool plane457GenSourceQRA plane457GenDeadQRA
    (by decide) plane457GenNoModel

end QiushiMatmul
