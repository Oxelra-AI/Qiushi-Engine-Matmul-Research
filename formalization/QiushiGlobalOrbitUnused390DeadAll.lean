import QiushiGlobalOrbitUnused390DeadBlock0
import QiushiGlobalOrbitUnused390DeadBlock1
import QiushiGlobalOrbitUnused390DeadBlock2
import QiushiGlobalOrbitUnused390DeadBlock3
import QiushiGlobalOrbitUnused390DeadBlock4
import QiushiGlobalOrbitUnused390DeadBlock5
import QiushiGlobalOrbitUnused390DeadBlock6
import QiushiGlobalOrbitUnused390DeadBlock7
import QiushiGlobalOrbitUnused390DeadBlock8
import QiushiGlobalOrbitUnused390DeadBlock9
import QiushiGlobalOrbitUnused390DeadBlock10
import QiushiGlobalOrbitUnused390DeadBlock11
import QiushiGlobalOrbitUnused390DeadBlock12
import QiushiGlobalOrbitUnused390DeadBlock13
import QiushiGlobalOrbitUnused390DeadBlock14
import QiushiGlobalOrbitUnused390DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane390UnusedGenDeadAll : forall i, plane390UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane390UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane390UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane390UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane390UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane390UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane390UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane390UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane390UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane390UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane390UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane390UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane390UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane390UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane390UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane390UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane390UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
