import QiushiPlane471LowerGenBool
import QiushiPlane471LowerGenTree
import QiushiPlane471LowerGenDispatch
namespace QiushiMatmul

theorem plane471LowerGen_lb17 :
    QuotientRankAtLeast (spanCodes [289, 84, 10]) 17 :=
  generic_plane_qra plane471LowerGenConfig plane471LowerGenBool plane471LowerGenSourceQRA plane471LowerGenDeadQRA
    (by decide) plane471LowerGenNoModel

end QiushiMatmul
