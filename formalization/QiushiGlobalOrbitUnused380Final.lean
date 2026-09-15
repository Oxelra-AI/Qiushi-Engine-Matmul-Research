import QiushiGlobalOrbitUnused380Bool
import QiushiGlobalOrbitUnused380Tree
import QiushiGlobalOrbitUnused380Dispatch
namespace QiushiMatmul

theorem plane380UnusedGen_lb17 :
    QuotientRankAtLeast (spanCodes [258, 68, 19, 10]) 17 :=
  generic_plane_qra plane380UnusedGenConfig plane380UnusedGenBool plane380UnusedGenSourceQRA plane380UnusedGenDeadQRA
    (by decide) plane380UnusedGenNoModel

end QiushiMatmul
