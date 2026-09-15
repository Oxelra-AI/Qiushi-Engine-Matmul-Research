import QiushiPlane476GenBool
import QiushiPlane476GenTree
import QiushiPlane476GenDispatch
namespace QiushiMatmul

theorem plane476Gen_lb18 :
    QuotientRankAtLeast (spanCodes [276, 96, 10]) 18 :=
  generic_plane_qra plane476GenConfig plane476GenBool plane476GenSourceQRA plane476GenDeadQRA
    (by decide) plane476GenNoModel

end QiushiMatmul
