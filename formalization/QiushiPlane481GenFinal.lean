import QiushiPlane481GenBool
import QiushiPlane481GenTree
import QiushiPlane481GenDispatch
namespace QiushiMatmul

theorem plane481Gen_lb18 :
    QuotientRankAtLeast (spanCodes [20, 1]) 18 :=
  generic_plane_qra plane481GenConfig plane481GenBool plane481GenSourceQRA plane481GenDeadQRA
    (by decide) plane481GenNoModel

end QiushiMatmul
