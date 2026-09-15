import QiushiGlobalOrbitUnused92Bool
import QiushiGlobalOrbitUnused92Tree
import QiushiGlobalOrbitUnused92Dispatch
namespace QiushiMatmul

theorem plane92UnusedGen_lb13 :
    QuotientRankAtLeast (spanCodes [160, 80, 4, 2, 1]) 13 :=
  generic_plane_qra plane92UnusedGenConfig plane92UnusedGenBool plane92UnusedGenSourceQRA plane92UnusedGenDeadQRA
    (by decide) plane92UnusedGenNoModel

end QiushiMatmul
