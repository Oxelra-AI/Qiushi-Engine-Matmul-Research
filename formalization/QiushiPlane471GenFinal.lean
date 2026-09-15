import QiushiPlane471GenBool
import QiushiPlane471GenTree
import QiushiPlane471GenDispatch
namespace QiushiMatmul

theorem plane471Gen_lb18 :
    QuotientRankAtLeast (spanCodes [289, 84, 10]) 18 :=
  generic_plane_qra plane471GenConfig plane471GenBool plane471GenSourceQRA plane471GenDeadQRA
    (by decide) plane471GenNoModel

end QiushiMatmul
