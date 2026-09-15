import QiushiGlobalOrbitUnused337DeadBlock0
import QiushiGlobalOrbitUnused337DeadBlock1
import QiushiGlobalOrbitUnused337DeadBlock2
import QiushiGlobalOrbitUnused337DeadBlock3
import QiushiGlobalOrbitUnused337DeadBlock4
import QiushiGlobalOrbitUnused337DeadBlock5
import QiushiGlobalOrbitUnused337DeadBlock6
import QiushiGlobalOrbitUnused337DeadBlock7
import QiushiGlobalOrbitUnused337DeadBlock8
import QiushiGlobalOrbitUnused337DeadBlock9
import QiushiGlobalOrbitUnused337DeadBlock10
import QiushiGlobalOrbitUnused337DeadBlock11
import QiushiGlobalOrbitUnused337DeadBlock12
import QiushiGlobalOrbitUnused337DeadBlock13
import QiushiGlobalOrbitUnused337DeadBlock14
import QiushiGlobalOrbitUnused337DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane337UnusedGenDeadAll : forall i, plane337UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane337UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane337UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane337UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane337UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane337UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane337UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane337UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane337UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane337UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane337UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane337UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane337UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane337UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane337UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane337UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane337UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
