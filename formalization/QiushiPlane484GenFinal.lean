import QiushiPlane484GenBool
import QiushiPlane484GenTree
import QiushiPlane484GenDispatch
namespace QiushiMatmul

theorem plane484Gen_lb19 :
    QuotientRankAtLeast (spanCodes [19, 10]) 19 :=
  generic_plane_qra plane484GenConfig plane484GenBool plane484GenSourceQRA plane484GenDeadQRA
    (by decide) plane484GenNoModel

end QiushiMatmul
