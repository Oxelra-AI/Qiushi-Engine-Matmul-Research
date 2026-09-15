import QiushiPlane465GenBool
import QiushiPlane465GenTree
import QiushiPlane465GenDispatch
namespace QiushiMatmul

theorem plane465Gen_lb18 :
    QuotientRankAtLeast (spanCodes [304, 68, 10]) 18 :=
  generic_plane_qra plane465GenConfig plane465GenBool plane465GenSourceQRA plane465GenDeadQRA
    (by decide) plane465GenNoModel

end QiushiMatmul
