import QiushiPlane428GenBool
import QiushiPlane428GenTree
import QiushiPlane428GenDispatch
namespace QiushiMatmul

theorem plane428Gen_lb17 :
    QuotientRankAtLeast (spanCodes [96, 16, 1]) 17 :=
  generic_plane_qra plane428GenConfig plane428GenBool plane428GenSourceQRA plane428GenDeadQRA
    (by decide) plane428GenNoModel

end QiushiMatmul
