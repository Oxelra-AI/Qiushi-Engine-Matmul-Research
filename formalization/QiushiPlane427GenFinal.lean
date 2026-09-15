import QiushiPlane427GenBool
import QiushiPlane427GenTree
import QiushiPlane427GenDispatch
namespace QiushiMatmul

theorem plane427Gen_lb17 :
    QuotientRankAtLeast (spanCodes [36, 16, 1]) 17 :=
  generic_plane_qra plane427GenConfig plane427GenBool plane427GenSourceQRA plane427GenDeadQRA
    (by decide) plane427GenNoModel

end QiushiMatmul
