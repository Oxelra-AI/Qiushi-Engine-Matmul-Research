import QiushiPlane491GenBool
import QiushiPlane491GenTree
import QiushiPlane491GenDispatch
namespace QiushiMatmul

theorem plane491Gen_lb19 :
    QuotientRankAtLeast (spanCodes [163, 84]) 19 :=
  generic_plane_qra plane491GenConfig plane491GenBool plane491GenSourceQRA plane491GenDeadQRA
    (by decide) plane491GenNoModel

end QiushiMatmul
