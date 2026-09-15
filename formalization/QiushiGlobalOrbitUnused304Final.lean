import QiushiGlobalOrbitUnused304Bool
import QiushiGlobalOrbitUnused304Tree
import QiushiGlobalOrbitUnused304Dispatch
namespace QiushiMatmul

theorem plane304UnusedGen_lb16 :
    QuotientRankAtLeast (spanCodes [256, 84, 10, 1]) 16 :=
  generic_plane_qra plane304UnusedGenConfig plane304UnusedGenBool plane304UnusedGenSourceQRA plane304UnusedGenDeadQRA
    (by decide) plane304UnusedGenNoModel

end QiushiMatmul
