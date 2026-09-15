import QiushiPlane459GenBool
import QiushiPlane459GenTree
import QiushiPlane459GenDispatch
namespace QiushiMatmul

theorem plane459Gen_lb18 :
    QuotientRankAtLeast (spanCodes [160, 68, 10]) 18 :=
  generic_plane_qra plane459GenConfig plane459GenBool plane459GenSourceQRA plane459GenDeadQRA
    (by decide) plane459GenNoModel

end QiushiMatmul
