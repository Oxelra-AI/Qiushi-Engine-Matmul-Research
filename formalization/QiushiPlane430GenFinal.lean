import QiushiPlane430GenBool
import QiushiPlane430GenTree
import QiushiPlane430GenDispatch
namespace QiushiMatmul

theorem plane430Gen_lb17 :
    QuotientRankAtLeast (spanCodes [100, 16, 1]) 17 :=
  generic_plane_qra plane430GenConfig plane430GenBool plane430GenSourceQRA plane430GenDeadQRA
    (by decide) plane430GenNoModel

end QiushiMatmul
