import QiushiGlobalOrbitUnused181DeadBlock0
import QiushiGlobalOrbitUnused181DeadBlock1
import QiushiGlobalOrbitUnused181DeadBlock2
import QiushiGlobalOrbitUnused181DeadBlock3
import QiushiGlobalOrbitUnused181DeadBlock4
import QiushiGlobalOrbitUnused181DeadBlock5
import QiushiGlobalOrbitUnused181DeadBlock6
import QiushiGlobalOrbitUnused181DeadBlock7
import QiushiGlobalOrbitUnused181DeadBlock8
import QiushiGlobalOrbitUnused181DeadBlock9
import QiushiGlobalOrbitUnused181DeadBlock10
import QiushiGlobalOrbitUnused181DeadBlock11
import QiushiGlobalOrbitUnused181DeadBlock12
import QiushiGlobalOrbitUnused181DeadBlock13
import QiushiGlobalOrbitUnused181DeadBlock14
import QiushiGlobalOrbitUnused181DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane181UnusedGenDeadAll : forall i, plane181UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane181UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane181UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane181UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane181UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane181UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane181UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane181UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane181UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane181UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane181UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane181UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane181UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane181UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane181UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane181UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane181UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
