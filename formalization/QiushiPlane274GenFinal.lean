import QiushiPlane274GenBool
import QiushiPlane274GenTree
import QiushiPlane274GenDispatch
namespace QiushiMatmul

theorem plane274Gen_lb16 :
    QuotientRankAtLeast (spanCodes [160, 80, 2, 1]) 16 :=
  generic_plane_qra plane274GenConfig plane274GenBool plane274GenSourceQRA plane274GenDeadQRA
    (by decide) plane274GenNoModel

end QiushiMatmul
