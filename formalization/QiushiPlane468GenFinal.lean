import QiushiPlane468GenBool
import QiushiPlane468GenTree
import QiushiPlane468GenDispatch
namespace QiushiMatmul

theorem plane468Gen_lb18 :
    QuotientRankAtLeast (spanCodes [164, 84, 10]) 18 :=
  generic_plane_qra plane468GenConfig plane468GenBool plane468GenSourceQRA plane468GenDeadQRA
    (by decide) plane468GenNoModel

end QiushiMatmul
