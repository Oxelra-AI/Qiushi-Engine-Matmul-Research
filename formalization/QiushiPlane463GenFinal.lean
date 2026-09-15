import QiushiPlane463GenBool
import QiushiPlane463GenTree
import QiushiPlane463GenDispatch
namespace QiushiMatmul

theorem plane463Gen_lb18 :
    QuotientRankAtLeast (spanCodes [179, 68, 10]) 18 :=
  generic_plane_qra plane463GenConfig plane463GenBool plane463GenSourceQRA plane463GenDeadQRA
    (by decide) plane463GenNoModel

end QiushiMatmul
