import QiushiGlobalOrbitUnused353DeadBlock0
import QiushiGlobalOrbitUnused353DeadBlock1
import QiushiGlobalOrbitUnused353DeadBlock2
import QiushiGlobalOrbitUnused353DeadBlock3
import QiushiGlobalOrbitUnused353DeadBlock4
import QiushiGlobalOrbitUnused353DeadBlock5
import QiushiGlobalOrbitUnused353DeadBlock6
import QiushiGlobalOrbitUnused353DeadBlock7
import QiushiGlobalOrbitUnused353DeadBlock8
import QiushiGlobalOrbitUnused353DeadBlock9
import QiushiGlobalOrbitUnused353DeadBlock10
import QiushiGlobalOrbitUnused353DeadBlock11
import QiushiGlobalOrbitUnused353DeadBlock12
import QiushiGlobalOrbitUnused353DeadBlock13
import QiushiGlobalOrbitUnused353DeadBlock14
import QiushiGlobalOrbitUnused353DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane353UnusedGenDeadAll : forall i, plane353UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane353UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane353UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane353UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane353UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane353UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane353UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane353UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane353UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane353UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane353UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane353UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane353UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane353UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane353UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane353UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane353UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
