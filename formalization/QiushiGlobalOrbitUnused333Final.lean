import QiushiGlobalOrbitUnused333Bool
import QiushiGlobalOrbitUnused333Tree
import QiushiGlobalOrbitUnused333Dispatch
namespace QiushiMatmul

theorem plane333UnusedGen_lb16 :
    QuotientRankAtLeast (spanCodes [298, 96, 16, 1]) 16 :=
  generic_plane_qra plane333UnusedGenConfig plane333UnusedGenBool plane333UnusedGenSourceQRA plane333UnusedGenDeadQRA
    (by decide) plane333UnusedGenNoModel

end QiushiMatmul
