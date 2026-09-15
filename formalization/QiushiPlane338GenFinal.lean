import QiushiPlane338GenBool
import QiushiPlane338GenTree
import QiushiPlane338GenDispatch
namespace QiushiMatmul

theorem plane338Gen_lb16 :
    QuotientRankAtLeast (spanCodes [288, 98, 16, 1]) 16 :=
  generic_plane_qra plane338GenConfig plane338GenBool plane338GenSourceQRA plane338GenDeadQRA
    (by decide) plane338GenNoModel

end QiushiMatmul
