import QiushiPlane456LowerGenBool
import QiushiPlane456LowerGenTree
import QiushiPlane456LowerGenDispatch
namespace QiushiMatmul

theorem plane456LowerGen_lb17 :
    QuotientRankAtLeast (spanCodes [161, 20, 10]) 17 :=
  generic_plane_qra plane456LowerGenConfig plane456LowerGenBool plane456LowerGenSourceQRA plane456LowerGenDeadQRA
    (by decide) plane456LowerGenNoModel

end QiushiMatmul
