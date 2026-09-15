import QiushiPlane433GenBool
import QiushiPlane433GenTree
import QiushiPlane433GenDispatch
namespace QiushiMatmul

theorem plane433Gen_lb17 :
    QuotientRankAtLeast (spanCodes [258, 16, 1]) 17 :=
  generic_plane_qra plane433GenConfig plane433GenBool plane433GenSourceQRA plane433GenDeadQRA
    (by decide) plane433GenNoModel

end QiushiMatmul
