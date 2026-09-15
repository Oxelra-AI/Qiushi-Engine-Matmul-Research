import QiushiPlane490GenBool
import QiushiPlane490GenTree
import QiushiPlane490GenDispatch
namespace QiushiMatmul

theorem plane490Gen_lb19 :
    QuotientRankAtLeast (spanCodes [275, 10]) 19 :=
  generic_plane_qra plane490GenConfig plane490GenBool plane490GenSourceQRA plane490GenDeadQRA
    (by decide) plane490GenNoModel

end QiushiMatmul
