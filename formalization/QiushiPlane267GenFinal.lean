import QiushiPlane267GenBool
import QiushiPlane267GenTree
import QiushiPlane267GenDispatch
namespace QiushiMatmul

theorem plane267Gen_lb16 :
    QuotientRankAtLeast (spanCodes [84, 32, 2, 1]) 16 :=
  generic_plane_qra plane267GenConfig plane267GenBool plane267GenSourceQRA plane267GenDeadQRA
    (by decide) plane267GenNoModel

end QiushiMatmul
