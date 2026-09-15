import QiushiGlobalOrbitUnused387Bool
import QiushiGlobalOrbitUnused387Tree
import QiushiGlobalOrbitUnused387Dispatch
namespace QiushiMatmul

theorem plane387UnusedGen_lb17 :
    QuotientRankAtLeast (spanCodes [162, 68, 20, 10]) 17 :=
  generic_plane_qra plane387UnusedGenConfig plane387UnusedGenBool plane387UnusedGenSourceQRA plane387UnusedGenDeadQRA
    (by decide) plane387UnusedGenNoModel

end QiushiMatmul
