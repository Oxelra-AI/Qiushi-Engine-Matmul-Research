import QiushiPlane449GenBool
import QiushiPlane449GenTree
import QiushiPlane449GenDispatch
namespace QiushiMatmul

theorem plane449Gen_lb17 :
    QuotientRankAtLeast (spanCodes [316, 160, 1]) 17 :=
  generic_plane_qra plane449GenConfig plane449GenBool plane449GenSourceQRA plane449GenDeadQRA
    (by decide) plane449GenNoModel

end QiushiMatmul
