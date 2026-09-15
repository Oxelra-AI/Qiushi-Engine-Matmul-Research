import QiushiPlane470GenBool
import QiushiPlane470GenTree
import QiushiPlane470GenDispatch
namespace QiushiMatmul

theorem plane470Gen_lb18 :
    QuotientRankAtLeast (spanCodes [259, 84, 10]) 18 :=
  generic_plane_qra plane470GenConfig plane470GenBool plane470GenSourceQRA plane470GenDeadQRA
    (by decide) plane470GenNoModel

end QiushiMatmul
