import QiushiPlane453GenBool
import QiushiPlane453GenTree
import QiushiPlane453GenDispatch
namespace QiushiMatmul

theorem plane453Gen_lb18 :
    QuotientRankAtLeast (spanCodes [68, 20, 10]) 18 :=
  generic_plane_qra plane453GenConfig plane453GenBool plane453GenSourceQRA plane453GenDeadQRA
    (by decide) plane453GenNoModel

end QiushiMatmul
