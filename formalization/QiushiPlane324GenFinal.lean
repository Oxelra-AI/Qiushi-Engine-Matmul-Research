import QiushiPlane324GenBool
import QiushiPlane324GenTree
import QiushiPlane324GenDispatch
namespace QiushiMatmul

theorem plane324Gen_lb16 :
    QuotientRankAtLeast (spanCodes [196, 36, 16, 1]) 16 :=
  generic_plane_qra plane324GenConfig plane324GenBool plane324GenSourceQRA plane324GenDeadQRA
    (by decide) plane324GenNoModel

end QiushiMatmul
