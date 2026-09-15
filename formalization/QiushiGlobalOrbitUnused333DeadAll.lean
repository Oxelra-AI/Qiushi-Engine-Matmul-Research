import QiushiGlobalOrbitUnused333DeadBlock0
import QiushiGlobalOrbitUnused333DeadBlock1
import QiushiGlobalOrbitUnused333DeadBlock2
import QiushiGlobalOrbitUnused333DeadBlock3
import QiushiGlobalOrbitUnused333DeadBlock4
import QiushiGlobalOrbitUnused333DeadBlock5
import QiushiGlobalOrbitUnused333DeadBlock6
import QiushiGlobalOrbitUnused333DeadBlock7
import QiushiGlobalOrbitUnused333DeadBlock8
import QiushiGlobalOrbitUnused333DeadBlock9
import QiushiGlobalOrbitUnused333DeadBlock10
import QiushiGlobalOrbitUnused333DeadBlock11
import QiushiGlobalOrbitUnused333DeadBlock12
import QiushiGlobalOrbitUnused333DeadBlock13
import QiushiGlobalOrbitUnused333DeadBlock14
import QiushiGlobalOrbitUnused333DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane333UnusedGenDeadAll : forall i, plane333UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane333UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane333UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane333UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane333UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane333UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane333UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane333UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane333UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane333UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane333UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane333UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane333UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane333UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane333UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane333UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane333UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
