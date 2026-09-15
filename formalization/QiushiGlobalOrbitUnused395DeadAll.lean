import QiushiGlobalOrbitUnused395DeadBlock0
import QiushiGlobalOrbitUnused395DeadBlock1
import QiushiGlobalOrbitUnused395DeadBlock2
import QiushiGlobalOrbitUnused395DeadBlock3
import QiushiGlobalOrbitUnused395DeadBlock4
import QiushiGlobalOrbitUnused395DeadBlock5
import QiushiGlobalOrbitUnused395DeadBlock6
import QiushiGlobalOrbitUnused395DeadBlock7
import QiushiGlobalOrbitUnused395DeadBlock8
import QiushiGlobalOrbitUnused395DeadBlock9
import QiushiGlobalOrbitUnused395DeadBlock10
import QiushiGlobalOrbitUnused395DeadBlock11
import QiushiGlobalOrbitUnused395DeadBlock12
import QiushiGlobalOrbitUnused395DeadBlock13
import QiushiGlobalOrbitUnused395DeadBlock14
import QiushiGlobalOrbitUnused395DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane395UnusedGenDeadAll : forall i, plane395UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane395UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane395UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane395UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane395UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane395UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane395UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane395UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane395UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane395UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane395UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane395UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane395UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane395UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane395UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane395UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane395UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
