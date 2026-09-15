import QiushiPlane434GenBool
import QiushiPlane434GenTree
import QiushiPlane434GenDispatch
namespace QiushiMatmul

theorem plane434Gen_lb17 :
    QuotientRankAtLeast (spanCodes [266, 16, 1]) 17 :=
  generic_plane_qra plane434GenConfig plane434GenBool plane434GenSourceQRA plane434GenDeadQRA
    (by decide) plane434GenNoModel

end QiushiMatmul
