import QiushiGlobalOrbitUnused184DeadBlock0
import QiushiGlobalOrbitUnused184DeadBlock1
import QiushiGlobalOrbitUnused184DeadBlock2
import QiushiGlobalOrbitUnused184DeadBlock3
import QiushiGlobalOrbitUnused184DeadBlock4
import QiushiGlobalOrbitUnused184DeadBlock5
import QiushiGlobalOrbitUnused184DeadBlock6
import QiushiGlobalOrbitUnused184DeadBlock7
import QiushiGlobalOrbitUnused184DeadBlock8
import QiushiGlobalOrbitUnused184DeadBlock9
import QiushiGlobalOrbitUnused184DeadBlock10
import QiushiGlobalOrbitUnused184DeadBlock11
import QiushiGlobalOrbitUnused184DeadBlock12
import QiushiGlobalOrbitUnused184DeadBlock13
import QiushiGlobalOrbitUnused184DeadBlock14
import QiushiGlobalOrbitUnused184DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane184UnusedGenDeadAll : forall i, plane184UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane184UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane184UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane184UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane184UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane184UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane184UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane184UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane184UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane184UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane184UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane184UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane184UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane184UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane184UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane184UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane184UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
