import QiushiPlane254GenBool
import QiushiPlane254GenTree
import QiushiPlane254GenDispatch
namespace QiushiMatmul

theorem plane254Gen_lb16 :
    QuotientRankAtLeast (spanCodes [84, 8, 2, 1]) 16 :=
  generic_plane_qra plane254GenConfig plane254GenBool plane254GenSourceQRA plane254GenDeadQRA
    (by decide) plane254GenNoModel

end QiushiMatmul
