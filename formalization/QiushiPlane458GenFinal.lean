import QiushiPlane458GenBool
import QiushiPlane458GenTree
import QiushiPlane458GenDispatch
namespace QiushiMatmul

theorem plane458Gen_lb18 :
    QuotientRankAtLeast (spanCodes [450, 20, 10]) 18 :=
  generic_plane_qra plane458GenConfig plane458GenBool plane458GenSourceQRA plane458GenDeadQRA
    (by decide) plane458GenNoModel

end QiushiMatmul
