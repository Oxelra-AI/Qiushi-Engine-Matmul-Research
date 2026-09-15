import QiushiPlane456GenBool
import QiushiPlane456GenTree
import QiushiPlane456GenDispatch
namespace QiushiMatmul

theorem plane456Gen_lb18 :
    QuotientRankAtLeast (spanCodes [161, 20, 10]) 18 :=
  generic_plane_qra plane456GenConfig plane456GenBool plane456GenSourceQRA plane456GenDeadQRA
    (by decide) plane456GenNoModel

end QiushiMatmul
