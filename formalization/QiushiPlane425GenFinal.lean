import QiushiPlane425GenBool
import QiushiPlane425GenTree
import QiushiPlane425GenDispatch
namespace QiushiMatmul

theorem plane425Gen_lb18 :
    QuotientRankAtLeast (spanCodes [258, 10, 1]) 18 :=
  generic_plane_qra plane425GenConfig plane425GenBool plane425GenSourceQRA plane425GenDeadQRA
    (by decide) plane425GenNoModel

end QiushiMatmul
