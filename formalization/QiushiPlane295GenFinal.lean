import QiushiPlane295GenBool
import QiushiPlane295GenTree
import QiushiPlane295GenDispatch
namespace QiushiMatmul

theorem plane295Gen_lb17 :
    QuotientRankAtLeast (spanCodes [272, 32, 10, 1]) 17 :=
  generic_plane_qra plane295GenConfig plane295GenBool plane295GenSourceQRA plane295GenDeadQRA
    (by decide) plane295GenNoModel

end QiushiMatmul
