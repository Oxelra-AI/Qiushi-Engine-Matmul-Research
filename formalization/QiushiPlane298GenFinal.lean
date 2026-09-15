import QiushiPlane298GenBool
import QiushiPlane298GenTree
import QiushiPlane298GenDispatch
namespace QiushiMatmul

theorem plane298Gen_lb16 :
    QuotientRankAtLeast (spanCodes [384, 32, 10, 1]) 16 :=
  generic_plane_qra plane298GenConfig plane298GenBool plane298GenSourceQRA plane298GenDeadQRA
    (by decide) plane298GenNoModel

end QiushiMatmul
