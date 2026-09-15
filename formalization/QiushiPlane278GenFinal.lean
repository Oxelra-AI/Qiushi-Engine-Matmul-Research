import QiushiPlane278GenBool
import QiushiPlane278GenTree
import QiushiPlane278GenDispatch
namespace QiushiMatmul

theorem plane278Gen_lb16 :
    QuotientRankAtLeast (spanCodes [304, 96, 2, 1]) 16 :=
  generic_plane_qra plane278GenConfig plane278GenBool plane278GenSourceQRA plane278GenDeadQRA
    (by decide) plane278GenNoModel

end QiushiMatmul
