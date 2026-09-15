import QiushiPlane336GenBool
import QiushiPlane336GenTree
import QiushiPlane336GenDispatch
namespace QiushiMatmul

theorem plane336Gen_lb16 :
    QuotientRankAtLeast (spanCodes [256, 98, 16, 1]) 16 :=
  generic_plane_qra plane336GenConfig plane336GenBool plane336GenSourceQRA plane336GenDeadQRA
    (by decide) plane336GenNoModel

end QiushiMatmul
