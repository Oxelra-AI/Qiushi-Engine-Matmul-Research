import QiushiPlane469GenBool
import QiushiPlane469GenTree
import QiushiPlane469GenDispatch
namespace QiushiMatmul

theorem plane469Gen_lb18 :
    QuotientRankAtLeast (spanCodes [258, 84, 10]) 18 :=
  generic_plane_qra plane469GenConfig plane469GenBool plane469GenSourceQRA plane469GenDeadQRA
    (by decide) plane469GenNoModel

end QiushiMatmul
