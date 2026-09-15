import QiushiGlobalOrbitUnused308DeadBlock0
import QiushiGlobalOrbitUnused308DeadBlock1
import QiushiGlobalOrbitUnused308DeadBlock2
import QiushiGlobalOrbitUnused308DeadBlock3
import QiushiGlobalOrbitUnused308DeadBlock4
import QiushiGlobalOrbitUnused308DeadBlock5
import QiushiGlobalOrbitUnused308DeadBlock6
import QiushiGlobalOrbitUnused308DeadBlock7
import QiushiGlobalOrbitUnused308DeadBlock8
import QiushiGlobalOrbitUnused308DeadBlock9
import QiushiGlobalOrbitUnused308DeadBlock10
import QiushiGlobalOrbitUnused308DeadBlock11
import QiushiGlobalOrbitUnused308DeadBlock12
import QiushiGlobalOrbitUnused308DeadBlock13
import QiushiGlobalOrbitUnused308DeadBlock14
import QiushiGlobalOrbitUnused308DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane308UnusedGenDeadAll : forall i, plane308UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane308UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane308UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane308UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane308UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane308UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane308UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane308UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane308UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane308UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane308UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane308UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane308UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane308UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane308UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane308UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane308UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
