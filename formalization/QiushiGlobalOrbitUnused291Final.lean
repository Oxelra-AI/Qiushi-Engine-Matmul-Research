import QiushiGlobalOrbitUnused291Bool
import QiushiGlobalOrbitUnused291Tree
import QiushiGlobalOrbitUnused291Dispatch
namespace QiushiMatmul

theorem plane291UnusedGen_lb16 :
    QuotientRankAtLeast (spanCodes [84, 32, 10, 1]) 16 :=
  generic_plane_qra plane291UnusedGenConfig plane291UnusedGenBool plane291UnusedGenSourceQRA plane291UnusedGenDeadQRA
    (by decide) plane291UnusedGenNoModel

end QiushiMatmul
