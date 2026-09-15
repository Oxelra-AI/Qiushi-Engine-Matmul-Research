import QiushiGlobalOrbitUnused273DeadBlock0
import QiushiGlobalOrbitUnused273DeadBlock1
import QiushiGlobalOrbitUnused273DeadBlock2
import QiushiGlobalOrbitUnused273DeadBlock3
import QiushiGlobalOrbitUnused273DeadBlock4
import QiushiGlobalOrbitUnused273DeadBlock5
import QiushiGlobalOrbitUnused273DeadBlock6
import QiushiGlobalOrbitUnused273DeadBlock7
import QiushiGlobalOrbitUnused273DeadBlock8
import QiushiGlobalOrbitUnused273DeadBlock9
import QiushiGlobalOrbitUnused273DeadBlock10
import QiushiGlobalOrbitUnused273DeadBlock11
import QiushiGlobalOrbitUnused273DeadBlock12
import QiushiGlobalOrbitUnused273DeadBlock13
import QiushiGlobalOrbitUnused273DeadBlock14
import QiushiGlobalOrbitUnused273DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane273UnusedGenDeadAll : forall i, plane273UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane273UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane273UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane273UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane273UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane273UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane273UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane273UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane273UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane273UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane273UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane273UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane273UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane273UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane273UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane273UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane273UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
