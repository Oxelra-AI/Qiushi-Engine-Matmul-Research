import QiushiPlane447GenBool
import QiushiPlane447GenTree
import QiushiPlane447GenDispatch
namespace QiushiMatmul

theorem plane447Gen_lb17 :
    QuotientRankAtLeast (spanCodes [306, 160, 1]) 17 :=
  generic_plane_qra plane447GenConfig plane447GenBool plane447GenSourceQRA plane447GenDeadQRA
    (by decide) plane447GenNoModel

end QiushiMatmul
