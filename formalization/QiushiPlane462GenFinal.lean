import QiushiPlane462GenBool
import QiushiPlane462GenTree
import QiushiPlane462GenDispatch
namespace QiushiMatmul

theorem plane462Gen_lb18 :
    QuotientRankAtLeast (spanCodes [178, 68, 10]) 18 :=
  generic_plane_qra plane462GenConfig plane462GenBool plane462GenSourceQRA plane462GenDeadQRA
    (by decide) plane462GenNoModel

end QiushiMatmul
