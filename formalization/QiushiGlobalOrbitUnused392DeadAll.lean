import QiushiGlobalOrbitUnused392DeadBlock0
import QiushiGlobalOrbitUnused392DeadBlock1
import QiushiGlobalOrbitUnused392DeadBlock2
import QiushiGlobalOrbitUnused392DeadBlock3
import QiushiGlobalOrbitUnused392DeadBlock4
import QiushiGlobalOrbitUnused392DeadBlock5
import QiushiGlobalOrbitUnused392DeadBlock6
import QiushiGlobalOrbitUnused392DeadBlock7
import QiushiGlobalOrbitUnused392DeadBlock8
import QiushiGlobalOrbitUnused392DeadBlock9
import QiushiGlobalOrbitUnused392DeadBlock10
import QiushiGlobalOrbitUnused392DeadBlock11
import QiushiGlobalOrbitUnused392DeadBlock12
import QiushiGlobalOrbitUnused392DeadBlock13
import QiushiGlobalOrbitUnused392DeadBlock14
import QiushiGlobalOrbitUnused392DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane392UnusedGenDeadAll : forall i, plane392UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane392UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane392UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane392UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane392UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane392UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane392UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane392UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane392UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane392UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane392UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane392UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane392UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane392UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane392UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane392UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane392UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
