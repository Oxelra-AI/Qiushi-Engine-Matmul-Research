import QiushiGlobalOrbitUnused328DeadBlock0
import QiushiGlobalOrbitUnused328DeadBlock1
import QiushiGlobalOrbitUnused328DeadBlock2
import QiushiGlobalOrbitUnused328DeadBlock3
import QiushiGlobalOrbitUnused328DeadBlock4
import QiushiGlobalOrbitUnused328DeadBlock5
import QiushiGlobalOrbitUnused328DeadBlock6
import QiushiGlobalOrbitUnused328DeadBlock7
import QiushiGlobalOrbitUnused328DeadBlock8
import QiushiGlobalOrbitUnused328DeadBlock9
import QiushiGlobalOrbitUnused328DeadBlock10
import QiushiGlobalOrbitUnused328DeadBlock11
import QiushiGlobalOrbitUnused328DeadBlock12
import QiushiGlobalOrbitUnused328DeadBlock13
import QiushiGlobalOrbitUnused328DeadBlock14
import QiushiGlobalOrbitUnused328DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane328UnusedGenDeadAll : forall i, plane328UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane328UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane328UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane328UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane328UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane328UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane328UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane328UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane328UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane328UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane328UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane328UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane328UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane328UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane328UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane328UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane328UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
