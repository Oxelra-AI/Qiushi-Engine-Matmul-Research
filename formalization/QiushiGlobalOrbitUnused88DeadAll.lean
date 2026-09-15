import QiushiGlobalOrbitUnused88DeadBlock0
import QiushiGlobalOrbitUnused88DeadBlock1
import QiushiGlobalOrbitUnused88DeadBlock2
import QiushiGlobalOrbitUnused88DeadBlock3
import QiushiGlobalOrbitUnused88DeadBlock4
import QiushiGlobalOrbitUnused88DeadBlock5
import QiushiGlobalOrbitUnused88DeadBlock6
import QiushiGlobalOrbitUnused88DeadBlock7
import QiushiGlobalOrbitUnused88DeadBlock8
import QiushiGlobalOrbitUnused88DeadBlock9
import QiushiGlobalOrbitUnused88DeadBlock10
import QiushiGlobalOrbitUnused88DeadBlock11
import QiushiGlobalOrbitUnused88DeadBlock12
import QiushiGlobalOrbitUnused88DeadBlock13
import QiushiGlobalOrbitUnused88DeadBlock14
import QiushiGlobalOrbitUnused88DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane88UnusedGenDeadAll : forall i, plane88UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane88UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane88UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane88UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane88UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane88UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane88UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane88UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane88UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane88UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane88UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane88UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane88UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane88UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane88UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane88UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane88UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
