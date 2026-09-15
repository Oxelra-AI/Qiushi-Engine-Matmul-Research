import QiushiGlobalOrbitUnused386DeadBlock0
import QiushiGlobalOrbitUnused386DeadBlock1
import QiushiGlobalOrbitUnused386DeadBlock2
import QiushiGlobalOrbitUnused386DeadBlock3
import QiushiGlobalOrbitUnused386DeadBlock4
import QiushiGlobalOrbitUnused386DeadBlock5
import QiushiGlobalOrbitUnused386DeadBlock6
import QiushiGlobalOrbitUnused386DeadBlock7
import QiushiGlobalOrbitUnused386DeadBlock8
import QiushiGlobalOrbitUnused386DeadBlock9
import QiushiGlobalOrbitUnused386DeadBlock10
import QiushiGlobalOrbitUnused386DeadBlock11
import QiushiGlobalOrbitUnused386DeadBlock12
import QiushiGlobalOrbitUnused386DeadBlock13
import QiushiGlobalOrbitUnused386DeadBlock14
import QiushiGlobalOrbitUnused386DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane386UnusedGenDeadAll : forall i, plane386UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane386UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane386UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane386UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane386UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane386UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane386UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane386UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane386UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane386UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane386UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane386UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane386UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane386UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane386UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane386UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane386UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
