import QiushiPlane269GenBool
import QiushiPlane269GenTree
import QiushiPlane269GenDispatch
namespace QiushiMatmul

theorem plane269Gen_lb16 :
    QuotientRankAtLeast (spanCodes [264, 32, 2, 1]) 16 :=
  generic_plane_qra plane269GenConfig plane269GenBool plane269GenSourceQRA plane269GenDeadQRA
    (by decide) plane269GenNoModel

end QiushiMatmul
