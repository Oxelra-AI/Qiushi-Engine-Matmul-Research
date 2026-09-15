import QiushiGlobalOrbitUnused389DeadBlock0
import QiushiGlobalOrbitUnused389DeadBlock1
import QiushiGlobalOrbitUnused389DeadBlock2
import QiushiGlobalOrbitUnused389DeadBlock3
import QiushiGlobalOrbitUnused389DeadBlock4
import QiushiGlobalOrbitUnused389DeadBlock5
import QiushiGlobalOrbitUnused389DeadBlock6
import QiushiGlobalOrbitUnused389DeadBlock7
import QiushiGlobalOrbitUnused389DeadBlock8
import QiushiGlobalOrbitUnused389DeadBlock9
import QiushiGlobalOrbitUnused389DeadBlock10
import QiushiGlobalOrbitUnused389DeadBlock11
import QiushiGlobalOrbitUnused389DeadBlock12
import QiushiGlobalOrbitUnused389DeadBlock13
import QiushiGlobalOrbitUnused389DeadBlock14
import QiushiGlobalOrbitUnused389DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane389UnusedGenDeadAll : forall i, plane389UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane389UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane389UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane389UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane389UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane389UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane389UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane389UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane389UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane389UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane389UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane389UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane389UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane389UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane389UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane389UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane389UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
