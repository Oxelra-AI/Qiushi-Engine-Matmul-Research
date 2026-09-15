import QiushiGlobalOrbitUnused203DeadBlock0
import QiushiGlobalOrbitUnused203DeadBlock1
import QiushiGlobalOrbitUnused203DeadBlock2
import QiushiGlobalOrbitUnused203DeadBlock3
import QiushiGlobalOrbitUnused203DeadBlock4
import QiushiGlobalOrbitUnused203DeadBlock5
import QiushiGlobalOrbitUnused203DeadBlock6
import QiushiGlobalOrbitUnused203DeadBlock7
import QiushiGlobalOrbitUnused203DeadBlock8
import QiushiGlobalOrbitUnused203DeadBlock9
import QiushiGlobalOrbitUnused203DeadBlock10
import QiushiGlobalOrbitUnused203DeadBlock11
import QiushiGlobalOrbitUnused203DeadBlock12
import QiushiGlobalOrbitUnused203DeadBlock13
import QiushiGlobalOrbitUnused203DeadBlock14
import QiushiGlobalOrbitUnused203DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane203UnusedGenDeadAll : forall i, plane203UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane203UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane203UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane203UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane203UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane203UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane203UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane203UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane203UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane203UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane203UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane203UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane203UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane203UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane203UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane203UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane203UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
