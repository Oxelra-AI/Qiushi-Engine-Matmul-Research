import QiushiGlobalOrbitUnused396DeadBlock0
import QiushiGlobalOrbitUnused396DeadBlock1
import QiushiGlobalOrbitUnused396DeadBlock2
import QiushiGlobalOrbitUnused396DeadBlock3
import QiushiGlobalOrbitUnused396DeadBlock4
import QiushiGlobalOrbitUnused396DeadBlock5
import QiushiGlobalOrbitUnused396DeadBlock6
import QiushiGlobalOrbitUnused396DeadBlock7
import QiushiGlobalOrbitUnused396DeadBlock8
import QiushiGlobalOrbitUnused396DeadBlock9
import QiushiGlobalOrbitUnused396DeadBlock10
import QiushiGlobalOrbitUnused396DeadBlock11
import QiushiGlobalOrbitUnused396DeadBlock12
import QiushiGlobalOrbitUnused396DeadBlock13
import QiushiGlobalOrbitUnused396DeadBlock14
import QiushiGlobalOrbitUnused396DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane396UnusedGenDeadAll : forall i, plane396UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane396UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane396UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane396UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane396UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane396UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane396UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane396UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane396UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane396UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane396UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane396UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane396UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane396UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane396UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane396UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane396UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
