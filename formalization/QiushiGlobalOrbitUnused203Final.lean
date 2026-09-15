import QiushiGlobalOrbitUnused203Bool
import QiushiGlobalOrbitUnused203Tree
import QiushiGlobalOrbitUnused203Dispatch
namespace QiushiMatmul

theorem plane203UnusedGen_lb16 :
    QuotientRankAtLeast (spanCodes [272, 176, 68, 10, 1]) 16 :=
  generic_plane_qra plane203UnusedGenConfig plane203UnusedGenBool plane203UnusedGenSourceQRA plane203UnusedGenDeadQRA
    (by decide) plane203UnusedGenNoModel

end QiushiMatmul
