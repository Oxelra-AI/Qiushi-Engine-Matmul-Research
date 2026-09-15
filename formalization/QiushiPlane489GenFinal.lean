import QiushiPlane489GenBool
import QiushiPlane489GenTree
import QiushiPlane489GenDispatch
namespace QiushiMatmul

theorem plane489Gen_lb19 :
    QuotientRankAtLeast (spanCodes [258, 10]) 19 :=
  generic_plane_qra plane489GenConfig plane489GenBool plane489GenSourceQRA plane489GenDeadQRA
    (by decide) plane489GenNoModel

end QiushiMatmul
