import QiushiPlane467GenBool
import QiushiPlane467GenTree
import QiushiPlane467GenDispatch
namespace QiushiMatmul

theorem plane467Gen_lb18 :
    QuotientRankAtLeast (spanCodes [163, 84, 10]) 18 :=
  generic_plane_qra plane467GenConfig plane467GenBool plane467GenSourceQRA plane467GenDeadQRA
    (by decide) plane467GenNoModel

end QiushiMatmul
