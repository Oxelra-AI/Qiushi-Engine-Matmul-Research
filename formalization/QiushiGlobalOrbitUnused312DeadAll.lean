import QiushiGlobalOrbitUnused312DeadBlock0
import QiushiGlobalOrbitUnused312DeadBlock1
import QiushiGlobalOrbitUnused312DeadBlock2
import QiushiGlobalOrbitUnused312DeadBlock3
import QiushiGlobalOrbitUnused312DeadBlock4
import QiushiGlobalOrbitUnused312DeadBlock5
import QiushiGlobalOrbitUnused312DeadBlock6
import QiushiGlobalOrbitUnused312DeadBlock7
import QiushiGlobalOrbitUnused312DeadBlock8
import QiushiGlobalOrbitUnused312DeadBlock9
import QiushiGlobalOrbitUnused312DeadBlock10
import QiushiGlobalOrbitUnused312DeadBlock11
import QiushiGlobalOrbitUnused312DeadBlock12
import QiushiGlobalOrbitUnused312DeadBlock13
import QiushiGlobalOrbitUnused312DeadBlock14
import QiushiGlobalOrbitUnused312DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane312UnusedGenDeadAll : forall i, plane312UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane312UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane312UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane312UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane312UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane312UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane312UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane312UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane312UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane312UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane312UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane312UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane312UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane312UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane312UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane312UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane312UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
