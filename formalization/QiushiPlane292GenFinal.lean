import QiushiPlane292GenBool
import QiushiPlane292GenTree
import QiushiPlane292GenDispatch
namespace QiushiMatmul

theorem plane292Gen_lb16 :
    QuotientRankAtLeast (spanCodes [128, 32, 10, 1]) 16 :=
  generic_plane_qra plane292GenConfig plane292GenBool plane292GenSourceQRA plane292GenDeadQRA
    (by decide) plane292GenNoModel

end QiushiMatmul
