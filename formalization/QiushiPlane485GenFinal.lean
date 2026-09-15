import QiushiPlane485GenBool
import QiushiPlane485GenTree
import QiushiPlane485GenDispatch
namespace QiushiMatmul

theorem plane485Gen_lb19 :
    QuotientRankAtLeast (spanCodes [20, 10]) 19 :=
  generic_plane_qra plane485GenConfig plane485GenBool plane485GenSourceQRA plane485GenDeadQRA
    (by decide) plane485GenNoModel

end QiushiMatmul
