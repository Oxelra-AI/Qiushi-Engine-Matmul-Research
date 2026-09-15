import QiushiPlane455GenBool
import QiushiPlane455GenTree
import QiushiPlane455GenDispatch
namespace QiushiMatmul

theorem plane455Gen_lb18 :
    QuotientRankAtLeast (spanCodes [129, 20, 10]) 18 :=
  generic_plane_qra plane455GenConfig plane455GenBool plane455GenSourceQRA plane455GenDeadQRA
    (by decide) plane455GenNoModel

end QiushiMatmul
