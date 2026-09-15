import QiushiGlobalOrbitUnused390Bool
import QiushiGlobalOrbitUnused390Tree
import QiushiGlobalOrbitUnused390Dispatch
namespace QiushiMatmul

theorem plane390UnusedGen_lb17 :
    QuotientRankAtLeast (spanCodes [167, 68, 20, 10]) 17 :=
  generic_plane_qra plane390UnusedGenConfig plane390UnusedGenBool plane390UnusedGenSourceQRA plane390UnusedGenDeadQRA
    (by decide) plane390UnusedGenNoModel

end QiushiMatmul
