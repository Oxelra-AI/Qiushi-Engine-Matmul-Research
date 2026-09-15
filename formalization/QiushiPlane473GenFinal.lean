import QiushiPlane473GenBool
import QiushiPlane473GenTree
import QiushiPlane473GenDispatch
namespace QiushiMatmul

theorem plane473Gen_lb18 :
    QuotientRankAtLeast (spanCodes [293, 84, 10]) 18 :=
  generic_plane_qra plane473GenConfig plane473GenBool plane473GenSourceQRA plane473GenDeadQRA
    (by decide) plane473GenNoModel

end QiushiMatmul
