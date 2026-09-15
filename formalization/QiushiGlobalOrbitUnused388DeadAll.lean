import QiushiGlobalOrbitUnused388DeadBlock0
import QiushiGlobalOrbitUnused388DeadBlock1
import QiushiGlobalOrbitUnused388DeadBlock2
import QiushiGlobalOrbitUnused388DeadBlock3
import QiushiGlobalOrbitUnused388DeadBlock4
import QiushiGlobalOrbitUnused388DeadBlock5
import QiushiGlobalOrbitUnused388DeadBlock6
import QiushiGlobalOrbitUnused388DeadBlock7
import QiushiGlobalOrbitUnused388DeadBlock8
import QiushiGlobalOrbitUnused388DeadBlock9
import QiushiGlobalOrbitUnused388DeadBlock10
import QiushiGlobalOrbitUnused388DeadBlock11
import QiushiGlobalOrbitUnused388DeadBlock12
import QiushiGlobalOrbitUnused388DeadBlock13
import QiushiGlobalOrbitUnused388DeadBlock14
import QiushiGlobalOrbitUnused388DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane388UnusedGenDeadAll : forall i, plane388UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane388UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane388UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane388UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane388UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane388UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane388UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane388UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane388UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane388UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane388UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane388UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane388UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane388UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane388UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane388UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane388UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
