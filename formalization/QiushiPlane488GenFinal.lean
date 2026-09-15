import QiushiPlane488GenBool
import QiushiPlane488GenTree
import QiushiPlane488GenDispatch
namespace QiushiMatmul

theorem plane488Gen_lb19 :
    QuotientRankAtLeast (spanCodes [96, 10]) 19 :=
  generic_plane_qra plane488GenConfig plane488GenBool plane488GenSourceQRA plane488GenDeadQRA
    (by decide) plane488GenNoModel

end QiushiMatmul
