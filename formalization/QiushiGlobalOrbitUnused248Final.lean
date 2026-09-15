import QiushiGlobalOrbitUnused248Bool
import QiushiGlobalOrbitUnused248Tree
import QiushiGlobalOrbitUnused248Dispatch
namespace QiushiMatmul

theorem plane248UnusedGen_lb14 :
    QuotientRankAtLeast (spanCodes [8, 4, 2, 1]) 14 :=
  generic_plane_qra plane248UnusedGenConfig plane248UnusedGenBool plane248UnusedGenSourceQRA plane248UnusedGenDeadQRA
    (by decide) plane248UnusedGenNoModel

end QiushiMatmul
