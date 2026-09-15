import QiushiPlane475GenBool
import QiushiPlane475GenTree
import QiushiPlane475GenDispatch
namespace QiushiMatmul

theorem plane475Gen_lb18 :
    QuotientRankAtLeast (spanCodes [165, 96, 10]) 18 :=
  generic_plane_qra plane475GenConfig plane475GenBool plane475GenSourceQRA plane475GenDeadQRA
    (by decide) plane475GenNoModel

end QiushiMatmul
