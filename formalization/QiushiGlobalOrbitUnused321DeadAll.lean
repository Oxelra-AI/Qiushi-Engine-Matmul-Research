import QiushiGlobalOrbitUnused321DeadBlock0
import QiushiGlobalOrbitUnused321DeadBlock1
import QiushiGlobalOrbitUnused321DeadBlock2
import QiushiGlobalOrbitUnused321DeadBlock3
import QiushiGlobalOrbitUnused321DeadBlock4
import QiushiGlobalOrbitUnused321DeadBlock5
import QiushiGlobalOrbitUnused321DeadBlock6
import QiushiGlobalOrbitUnused321DeadBlock7
import QiushiGlobalOrbitUnused321DeadBlock8
import QiushiGlobalOrbitUnused321DeadBlock9
import QiushiGlobalOrbitUnused321DeadBlock10
import QiushiGlobalOrbitUnused321DeadBlock11
import QiushiGlobalOrbitUnused321DeadBlock12
import QiushiGlobalOrbitUnused321DeadBlock13
import QiushiGlobalOrbitUnused321DeadBlock14
import QiushiGlobalOrbitUnused321DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane321UnusedGenDeadAll : forall i, plane321UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane321UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane321UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane321UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane321UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane321UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane321UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane321UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane321UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane321UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane321UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane321UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane321UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane321UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane321UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane321UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane321UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
