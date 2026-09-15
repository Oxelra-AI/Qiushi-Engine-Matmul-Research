import QiushiGlobalOrbitUnused291DeadBlock0
import QiushiGlobalOrbitUnused291DeadBlock1
import QiushiGlobalOrbitUnused291DeadBlock2
import QiushiGlobalOrbitUnused291DeadBlock3
import QiushiGlobalOrbitUnused291DeadBlock4
import QiushiGlobalOrbitUnused291DeadBlock5
import QiushiGlobalOrbitUnused291DeadBlock6
import QiushiGlobalOrbitUnused291DeadBlock7
import QiushiGlobalOrbitUnused291DeadBlock8
import QiushiGlobalOrbitUnused291DeadBlock9
import QiushiGlobalOrbitUnused291DeadBlock10
import QiushiGlobalOrbitUnused291DeadBlock11
import QiushiGlobalOrbitUnused291DeadBlock12
import QiushiGlobalOrbitUnused291DeadBlock13
import QiushiGlobalOrbitUnused291DeadBlock14
import QiushiGlobalOrbitUnused291DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane291UnusedGenDeadAll : forall i, plane291UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane291UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane291UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane291UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane291UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane291UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane291UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane291UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane291UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane291UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane291UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane291UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane291UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane291UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane291UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane291UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane291UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
