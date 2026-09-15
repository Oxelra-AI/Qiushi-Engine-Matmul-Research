import QiushiPlane477GenBool
import QiushiPlane477GenTree
import QiushiPlane477GenDispatch
namespace QiushiMatmul

theorem plane477Gen_lb18 :
    QuotientRankAtLeast (spanCodes [286, 163, 84]) 18 :=
  generic_plane_qra plane477GenConfig plane477GenBool plane477GenSourceQRA plane477GenDeadQRA
    (by decide) plane477GenNoModel

end QiushiMatmul
