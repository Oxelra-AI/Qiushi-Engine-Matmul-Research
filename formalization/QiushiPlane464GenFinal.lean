import QiushiPlane464GenBool
import QiushiPlane464GenTree
import QiushiPlane464GenDispatch
namespace QiushiMatmul

theorem plane464Gen_lb18 :
    QuotientRankAtLeast (spanCodes [180, 68, 10]) 18 :=
  generic_plane_qra plane464GenConfig plane464GenBool plane464GenSourceQRA plane464GenDeadQRA
    (by decide) plane464GenNoModel

end QiushiMatmul
