import QiushiGlobalOrbitUnused284DeadBlock0
import QiushiGlobalOrbitUnused284DeadBlock1
import QiushiGlobalOrbitUnused284DeadBlock2
import QiushiGlobalOrbitUnused284DeadBlock3
import QiushiGlobalOrbitUnused284DeadBlock4
import QiushiGlobalOrbitUnused284DeadBlock5
import QiushiGlobalOrbitUnused284DeadBlock6
import QiushiGlobalOrbitUnused284DeadBlock7
import QiushiGlobalOrbitUnused284DeadBlock8
import QiushiGlobalOrbitUnused284DeadBlock9
import QiushiGlobalOrbitUnused284DeadBlock10
import QiushiGlobalOrbitUnused284DeadBlock11
import QiushiGlobalOrbitUnused284DeadBlock12
import QiushiGlobalOrbitUnused284DeadBlock13
import QiushiGlobalOrbitUnused284DeadBlock14
import QiushiGlobalOrbitUnused284DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane284UnusedGenDeadAll : forall i, plane284UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane284UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane284UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane284UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane284UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane284UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane284UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane284UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane284UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane284UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane284UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane284UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane284UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane284UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane284UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane284UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane284UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
