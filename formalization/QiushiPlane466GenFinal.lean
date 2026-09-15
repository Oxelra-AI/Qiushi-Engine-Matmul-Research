import QiushiPlane466GenBool
import QiushiPlane466GenTree
import QiushiPlane466GenDispatch
namespace QiushiMatmul

theorem plane466Gen_lb18 :
    QuotientRankAtLeast (spanCodes [305, 68, 10]) 18 :=
  generic_plane_qra plane466GenConfig plane466GenBool plane466GenSourceQRA plane466GenDeadQRA
    (by decide) plane466GenNoModel

end QiushiMatmul
