import QiushiPlane480GenBool
import QiushiPlane480GenTree
import QiushiPlane480GenDispatch
namespace QiushiMatmul

theorem plane480Gen_lb18 :
    QuotientRankAtLeast (spanCodes [16, 1]) 18 :=
  generic_plane_qra plane480GenConfig plane480GenBool plane480GenSourceQRA plane480GenDeadQRA
    (by decide) plane480GenNoModel

end QiushiMatmul
