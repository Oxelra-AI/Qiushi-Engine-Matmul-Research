import QiushiPlane429GenBool
import QiushiPlane429GenTree
import QiushiPlane429GenDispatch
namespace QiushiMatmul

theorem plane429Gen_lb17 :
    QuotientRankAtLeast (spanCodes [98, 16, 1]) 17 :=
  generic_plane_qra plane429GenConfig plane429GenBool plane429GenSourceQRA plane429GenDeadQRA
    (by decide) plane429GenNoModel

end QiushiMatmul
