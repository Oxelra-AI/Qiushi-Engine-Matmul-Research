import QiushiGlobalOrbitUnused386Bool
import QiushiGlobalOrbitUnused386Tree
import QiushiGlobalOrbitUnused386Dispatch
namespace QiushiMatmul

theorem plane386UnusedGen_lb17 :
    QuotientRankAtLeast (spanCodes [161, 68, 20, 10]) 17 :=
  generic_plane_qra plane386UnusedGenConfig plane386UnusedGenBool plane386UnusedGenSourceQRA plane386UnusedGenDeadQRA
    (by decide) plane386UnusedGenNoModel

end QiushiMatmul
