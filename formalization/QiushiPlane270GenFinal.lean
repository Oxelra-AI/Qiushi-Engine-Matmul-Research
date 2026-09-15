import QiushiPlane270GenBool
import QiushiPlane270GenTree
import QiushiPlane270GenDispatch
namespace QiushiMatmul

theorem plane270Gen_lb15 :
    QuotientRankAtLeast (spanCodes [320, 32, 2, 1]) 15 :=
  generic_plane_qra plane270GenConfig plane270GenBool plane270GenSourceQRA plane270GenDeadQRA
    (by decide) plane270GenNoModel

end QiushiMatmul
