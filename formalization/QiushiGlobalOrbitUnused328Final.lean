import QiushiGlobalOrbitUnused328Bool
import QiushiGlobalOrbitUnused328Tree
import QiushiGlobalOrbitUnused328Dispatch
namespace QiushiMatmul

theorem plane328UnusedGen_lb16 :
    QuotientRankAtLeast (spanCodes [140, 96, 16, 1]) 16 :=
  generic_plane_qra plane328UnusedGenConfig plane328UnusedGenBool plane328UnusedGenSourceQRA plane328UnusedGenDeadQRA
    (by decide) plane328UnusedGenNoModel

end QiushiMatmul
