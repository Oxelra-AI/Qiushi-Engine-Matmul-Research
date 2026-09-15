import QiushiGlobalOrbitUnused406Bool
import QiushiGlobalOrbitUnused406Tree
import QiushiGlobalOrbitUnused406Dispatch
namespace QiushiMatmul

theorem plane406UnusedGen_lb17 :
    QuotientRankAtLeast (spanCodes [276, 179, 68, 10]) 17 :=
  generic_plane_qra plane406UnusedGenConfig plane406UnusedGenBool plane406UnusedGenSourceQRA plane406UnusedGenDeadQRA
    (by decide) plane406UnusedGenNoModel

end QiushiMatmul
