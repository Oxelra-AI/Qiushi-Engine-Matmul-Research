import QiushiPlane463LowerGenBool
import QiushiPlane463LowerGenTree
import QiushiPlane463LowerGenDispatch
namespace QiushiMatmul

theorem plane463LowerGen_lb17 :
    QuotientRankAtLeast (spanCodes [179, 68, 10]) 17 :=
  generic_plane_qra plane463LowerGenConfig plane463LowerGenBool plane463LowerGenSourceQRA plane463LowerGenDeadQRA
    (by decide) plane463LowerGenNoModel

end QiushiMatmul
