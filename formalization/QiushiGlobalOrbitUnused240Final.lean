import QiushiGlobalOrbitUnused240Bool
import QiushiGlobalOrbitUnused240Tree
import QiushiGlobalOrbitUnused240Dispatch
namespace QiushiMatmul

theorem plane240UnusedGen_lb16 :
    QuotientRankAtLeast (spanCodes [261, 161, 68, 19, 10]) 16 :=
  generic_plane_qra plane240UnusedGenConfig plane240UnusedGenBool plane240UnusedGenSourceQRA plane240UnusedGenDeadQRA
    (by decide) plane240UnusedGenNoModel

end QiushiMatmul
