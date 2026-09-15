import QiushiGlobalOrbitUnused394DeadBlock0
import QiushiGlobalOrbitUnused394DeadBlock1
import QiushiGlobalOrbitUnused394DeadBlock2
import QiushiGlobalOrbitUnused394DeadBlock3
import QiushiGlobalOrbitUnused394DeadBlock4
import QiushiGlobalOrbitUnused394DeadBlock5
import QiushiGlobalOrbitUnused394DeadBlock6
import QiushiGlobalOrbitUnused394DeadBlock7
import QiushiGlobalOrbitUnused394DeadBlock8
import QiushiGlobalOrbitUnused394DeadBlock9
import QiushiGlobalOrbitUnused394DeadBlock10
import QiushiGlobalOrbitUnused394DeadBlock11
import QiushiGlobalOrbitUnused394DeadBlock12
import QiushiGlobalOrbitUnused394DeadBlock13
import QiushiGlobalOrbitUnused394DeadBlock14
import QiushiGlobalOrbitUnused394DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane394UnusedGenDeadAll : forall i, plane394UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane394UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane394UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane394UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane394UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane394UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane394UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane394UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane394UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane394UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane394UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane394UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane394UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane394UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane394UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane394UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane394UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
