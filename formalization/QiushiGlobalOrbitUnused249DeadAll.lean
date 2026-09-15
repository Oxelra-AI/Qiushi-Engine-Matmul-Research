import QiushiGlobalOrbitUnused249DeadBlock0
import QiushiGlobalOrbitUnused249DeadBlock1
import QiushiGlobalOrbitUnused249DeadBlock2
import QiushiGlobalOrbitUnused249DeadBlock3
import QiushiGlobalOrbitUnused249DeadBlock4
import QiushiGlobalOrbitUnused249DeadBlock5
import QiushiGlobalOrbitUnused249DeadBlock6
import QiushiGlobalOrbitUnused249DeadBlock7
import QiushiGlobalOrbitUnused249DeadBlock8
import QiushiGlobalOrbitUnused249DeadBlock9
import QiushiGlobalOrbitUnused249DeadBlock10
import QiushiGlobalOrbitUnused249DeadBlock11
import QiushiGlobalOrbitUnused249DeadBlock12
import QiushiGlobalOrbitUnused249DeadBlock13
import QiushiGlobalOrbitUnused249DeadBlock14
import QiushiGlobalOrbitUnused249DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane249UnusedGenDeadAll : forall i, plane249UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane249UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane249UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane249UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane249UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane249UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane249UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane249UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane249UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane249UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane249UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane249UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane249UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane249UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane249UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane249UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane249UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
