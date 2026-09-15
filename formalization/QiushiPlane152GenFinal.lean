import QiushiPlane152GenBool
import QiushiPlane152GenTree
import QiushiPlane152GenDispatch
namespace QiushiMatmul

theorem plane152Gen_lb16 :
    QuotientRankAtLeast (spanCodes [164, 96, 16, 10, 1]) 16 :=
  generic_plane_qra plane152GenConfig plane152GenBool plane152GenSourceQRA plane152GenDeadQRA
    (by decide) plane152GenNoModel

end QiushiMatmul
