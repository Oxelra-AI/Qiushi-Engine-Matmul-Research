import QiushiGlobalOrbitUnused240DeadBlock0
import QiushiGlobalOrbitUnused240DeadBlock1
import QiushiGlobalOrbitUnused240DeadBlock2
import QiushiGlobalOrbitUnused240DeadBlock3
import QiushiGlobalOrbitUnused240DeadBlock4
import QiushiGlobalOrbitUnused240DeadBlock5
import QiushiGlobalOrbitUnused240DeadBlock6
import QiushiGlobalOrbitUnused240DeadBlock7
import QiushiGlobalOrbitUnused240DeadBlock8
import QiushiGlobalOrbitUnused240DeadBlock9
import QiushiGlobalOrbitUnused240DeadBlock10
import QiushiGlobalOrbitUnused240DeadBlock11
import QiushiGlobalOrbitUnused240DeadBlock12
import QiushiGlobalOrbitUnused240DeadBlock13
import QiushiGlobalOrbitUnused240DeadBlock14
import QiushiGlobalOrbitUnused240DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane240UnusedGenDeadAll : forall i, plane240UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane240UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane240UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane240UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane240UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane240UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane240UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane240UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane240UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane240UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane240UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane240UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane240UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane240UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane240UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane240UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane240UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
