import QiushiGlobalOrbitUnused305Bool
import QiushiGlobalOrbitUnused305Tree
import QiushiGlobalOrbitUnused305Dispatch
namespace QiushiMatmul

theorem plane305UnusedGen_lb17 :
    QuotientRankAtLeast (spanCodes [258, 84, 10, 1]) 17 :=
  generic_plane_qra plane305UnusedGenConfig plane305UnusedGenBool plane305UnusedGenSourceQRA plane305UnusedGenDeadQRA
    (by decide) plane305UnusedGenNoModel

end QiushiMatmul
