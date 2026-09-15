import QiushiPlane461GenBool
import QiushiPlane461GenTree
import QiushiPlane461GenDispatch
namespace QiushiMatmul

theorem plane461Gen_lb18 :
    QuotientRankAtLeast (spanCodes [162, 68, 10]) 18 :=
  generic_plane_qra plane461GenConfig plane461GenBool plane461GenSourceQRA plane461GenDeadQRA
    (by decide) plane461GenNoModel

end QiushiMatmul
