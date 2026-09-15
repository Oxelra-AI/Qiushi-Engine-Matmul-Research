import QiushiPlane472GenBool
import QiushiPlane472GenTree
import QiushiPlane472GenDispatch
namespace QiushiMatmul

theorem plane472Gen_lb18 :
    QuotientRankAtLeast (spanCodes [290, 84, 10]) 18 :=
  generic_plane_qra plane472GenConfig plane472GenBool plane472GenSourceQRA plane472GenDeadQRA
    (by decide) plane472GenNoModel

end QiushiMatmul
