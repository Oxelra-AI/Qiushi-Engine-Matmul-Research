import QiushiPlane255GenBool
import QiushiPlane255GenTree
import QiushiPlane255GenDispatch
namespace QiushiMatmul

theorem plane255Gen_lb16 :
    QuotientRankAtLeast (spanCodes [96, 8, 2, 1]) 16 :=
  generic_plane_qra plane255GenConfig plane255GenBool plane255GenSourceQRA plane255GenDeadQRA
    (by decide) plane255GenNoModel

end QiushiMatmul
