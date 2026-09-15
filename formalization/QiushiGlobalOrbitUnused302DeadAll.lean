import QiushiGlobalOrbitUnused302DeadBlock0
import QiushiGlobalOrbitUnused302DeadBlock1
import QiushiGlobalOrbitUnused302DeadBlock2
import QiushiGlobalOrbitUnused302DeadBlock3
import QiushiGlobalOrbitUnused302DeadBlock4
import QiushiGlobalOrbitUnused302DeadBlock5
import QiushiGlobalOrbitUnused302DeadBlock6
import QiushiGlobalOrbitUnused302DeadBlock7
import QiushiGlobalOrbitUnused302DeadBlock8
import QiushiGlobalOrbitUnused302DeadBlock9
import QiushiGlobalOrbitUnused302DeadBlock10
import QiushiGlobalOrbitUnused302DeadBlock11
import QiushiGlobalOrbitUnused302DeadBlock12
import QiushiGlobalOrbitUnused302DeadBlock13
import QiushiGlobalOrbitUnused302DeadBlock14
import QiushiGlobalOrbitUnused302DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane302UnusedGenDeadAll : forall i, plane302UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane302UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane302UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane302UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane302UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane302UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane302UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane302UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane302UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane302UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane302UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane302UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane302UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane302UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane302UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane302UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane302UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
