import QiushiGlobalOrbitUnused401Bool
import QiushiGlobalOrbitUnused401Tree
import QiushiGlobalOrbitUnused401Dispatch
namespace QiushiMatmul

theorem plane401UnusedGen_lb17 :
    QuotientRankAtLeast (spanCodes [261, 96, 20, 10]) 17 :=
  generic_plane_qra plane401UnusedGenConfig plane401UnusedGenBool plane401UnusedGenSourceQRA plane401UnusedGenDeadQRA
    (by decide) plane401UnusedGenNoModel

end QiushiMatmul
