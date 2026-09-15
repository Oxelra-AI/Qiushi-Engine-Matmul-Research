import QiushiPlane470LowerGenBool
import QiushiPlane470LowerGenTree
import QiushiPlane470LowerGenDispatch
namespace QiushiMatmul

theorem plane470LowerGen_lb17 :
    QuotientRankAtLeast (spanCodes [259, 84, 10]) 17 :=
  generic_plane_qra plane470LowerGenConfig plane470LowerGenBool plane470LowerGenSourceQRA plane470LowerGenDeadQRA
    (by decide) plane470LowerGenNoModel

end QiushiMatmul
