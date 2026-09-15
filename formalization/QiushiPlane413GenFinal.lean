import QiushiPlane413GenBool
import QiushiPlane413GenTree
import QiushiPlane413GenDispatch
namespace QiushiMatmul

theorem plane413Gen_lb16 :
    QuotientRankAtLeast (spanCodes [32, 2, 1]) 16 :=
  generic_plane_qra plane413GenConfig plane413GenBool plane413GenSourceQRA plane413GenDeadQRA
    (by decide) plane413GenNoModel

end QiushiMatmul
