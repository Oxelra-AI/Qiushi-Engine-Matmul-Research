import QiushiPlane487GenBool
import QiushiPlane487GenTree
import QiushiPlane487GenDispatch
namespace QiushiMatmul

theorem plane487Gen_lb19 :
    QuotientRankAtLeast (spanCodes [84, 10]) 19 :=
  generic_plane_qra plane487GenConfig plane487GenBool plane487GenSourceQRA plane487GenDeadQRA
    (by decide) plane487GenNoModel

end QiushiMatmul
