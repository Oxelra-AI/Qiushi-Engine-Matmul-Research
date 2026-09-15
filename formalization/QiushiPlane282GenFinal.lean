import QiushiPlane282GenBool
import QiushiPlane282GenTree
import QiushiPlane282GenDispatch

namespace QiushiMatmul

theorem plane282Gen_lb17
    : QuotientRankAtLeast (spanCodes [258, 16, 10, 1]) 17 :=
  generic_plane_qra
    plane282GenConfig
    plane282GenBool
    plane282GenSourceQRA
    plane282GenDeadQRA
    (by decide)
    plane282GenNoModel

end QiushiMatmul
