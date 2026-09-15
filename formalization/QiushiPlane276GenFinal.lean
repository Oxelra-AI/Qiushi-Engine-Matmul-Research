import QiushiPlane276GenBool
import QiushiPlane276GenTree
import QiushiPlane276GenDispatch
namespace QiushiMatmul

theorem plane276Gen_lb16 :
    QuotientRankAtLeast (spanCodes [272, 96, 2, 1]) 16 :=
  generic_plane_qra plane276GenConfig plane276GenBool plane276GenSourceQRA plane276GenDeadQRA
    (by decide) plane276GenNoModel

end QiushiMatmul
