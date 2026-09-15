import QiushiGlobalOrbitUnused308Bool
import QiushiGlobalOrbitUnused308Tree
import QiushiGlobalOrbitUnused308Dispatch
namespace QiushiMatmul

theorem plane308UnusedGen_lb16 :
    QuotientRankAtLeast (spanCodes [288, 96, 10, 1]) 16 :=
  generic_plane_qra plane308UnusedGenConfig plane308UnusedGenBool plane308UnusedGenSourceQRA plane308UnusedGenDeadQRA
    (by decide) plane308UnusedGenNoModel

end QiushiMatmul
