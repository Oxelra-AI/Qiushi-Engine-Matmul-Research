import QiushiPlane454GenBool
import QiushiPlane454GenTree
import QiushiPlane454GenDispatch
namespace QiushiMatmul

theorem plane454Gen_lb18 :
    QuotientRankAtLeast (spanCodes [96, 20, 10]) 18 :=
  generic_plane_qra plane454GenConfig plane454GenBool plane454GenSourceQRA plane454GenDeadQRA
    (by decide) plane454GenNoModel

end QiushiMatmul
