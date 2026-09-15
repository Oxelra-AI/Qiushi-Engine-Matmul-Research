import QiushiPlane315GenBool
import QiushiPlane315GenTree
import QiushiPlane315GenDispatch
namespace QiushiMatmul

theorem plane315Gen_lb17 :
    QuotientRankAtLeast (spanCodes [260, 160, 10, 1]) 17 :=
  generic_plane_qra plane315GenConfig plane315GenBool plane315GenSourceQRA plane315GenDeadQRA
    (by decide) plane315GenNoModel

end QiushiMatmul
