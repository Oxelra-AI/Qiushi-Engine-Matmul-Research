import QiushiPlane474GenBool
import QiushiPlane474GenTree
import QiushiPlane474GenDispatch
namespace QiushiMatmul

theorem plane474Gen_lb18 :
    QuotientRankAtLeast (spanCodes [294, 84, 10]) 18 :=
  generic_plane_qra plane474GenConfig plane474GenBool plane474GenSourceQRA plane474GenDeadQRA
    (by decide) plane474GenNoModel

end QiushiMatmul
