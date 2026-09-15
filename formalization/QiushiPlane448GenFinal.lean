import QiushiPlane448GenBool
import QiushiPlane448GenTree
import QiushiPlane448GenDispatch
namespace QiushiMatmul

theorem plane448Gen_lb17 :
    QuotientRankAtLeast (spanCodes [314, 160, 1]) 17 :=
  generic_plane_qra plane448GenConfig plane448GenBool plane448GenSourceQRA plane448GenDeadQRA
    (by decide) plane448GenNoModel

end QiushiMatmul
