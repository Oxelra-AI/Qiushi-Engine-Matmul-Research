import QiushiGlobalOrbitUnused301DeadBlock0
import QiushiGlobalOrbitUnused301DeadBlock1
import QiushiGlobalOrbitUnused301DeadBlock2
import QiushiGlobalOrbitUnused301DeadBlock3
import QiushiGlobalOrbitUnused301DeadBlock4
import QiushiGlobalOrbitUnused301DeadBlock5
import QiushiGlobalOrbitUnused301DeadBlock6
import QiushiGlobalOrbitUnused301DeadBlock7
import QiushiGlobalOrbitUnused301DeadBlock8
import QiushiGlobalOrbitUnused301DeadBlock9
import QiushiGlobalOrbitUnused301DeadBlock10
import QiushiGlobalOrbitUnused301DeadBlock11
import QiushiGlobalOrbitUnused301DeadBlock12
import QiushiGlobalOrbitUnused301DeadBlock13
import QiushiGlobalOrbitUnused301DeadBlock14
import QiushiGlobalOrbitUnused301DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane301UnusedGenDeadAll : forall i, plane301UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane301UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane301UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane301UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane301UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane301UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane301UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane301UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane301UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane301UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane301UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane301UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane301UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane301UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane301UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane301UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane301UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
