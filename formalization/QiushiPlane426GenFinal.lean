import QiushiPlane426GenBool
import QiushiPlane426GenTree
import QiushiPlane426GenDispatch
namespace QiushiMatmul

theorem plane426Gen_lb18 :
    QuotientRankAtLeast (spanCodes [272, 10, 1]) 18 :=
  generic_plane_qra plane426GenConfig plane426GenBool plane426GenSourceQRA plane426GenDeadQRA
    (by decide) plane426GenNoModel

end QiushiMatmul
