import QiushiPlane275GenBool
import QiushiPlane275GenTree
import QiushiPlane275GenDispatch
namespace QiushiMatmul

theorem plane275Gen_lb16 :
    QuotientRankAtLeast (spanCodes [160, 84, 2, 1]) 16 :=
  generic_plane_qra plane275GenConfig plane275GenBool plane275GenSourceQRA plane275GenDeadQRA
    (by decide) plane275GenNoModel

end QiushiMatmul
