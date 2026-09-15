import QiushiPlane439GenBool
import QiushiPlane439GenTree
import QiushiPlane439GenDispatch
namespace QiushiMatmul

theorem plane439Gen_lb17 :
    QuotientRankAtLeast (spanCodes [160, 20, 1]) 17 :=
  generic_plane_qra plane439GenConfig plane439GenBool plane439GenSourceQRA plane439GenDeadQRA
    (by decide) plane439GenNoModel

end QiushiMatmul
