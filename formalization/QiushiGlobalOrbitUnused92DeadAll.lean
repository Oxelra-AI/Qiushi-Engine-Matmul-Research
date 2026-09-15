import QiushiGlobalOrbitUnused92DeadBlock0
import QiushiGlobalOrbitUnused92DeadBlock1
import QiushiGlobalOrbitUnused92DeadBlock2
import QiushiGlobalOrbitUnused92DeadBlock3
import QiushiGlobalOrbitUnused92DeadBlock4
import QiushiGlobalOrbitUnused92DeadBlock5
import QiushiGlobalOrbitUnused92DeadBlock6
import QiushiGlobalOrbitUnused92DeadBlock7
import QiushiGlobalOrbitUnused92DeadBlock8
import QiushiGlobalOrbitUnused92DeadBlock9
import QiushiGlobalOrbitUnused92DeadBlock10
import QiushiGlobalOrbitUnused92DeadBlock11
import QiushiGlobalOrbitUnused92DeadBlock12
import QiushiGlobalOrbitUnused92DeadBlock13
import QiushiGlobalOrbitUnused92DeadBlock14
import QiushiGlobalOrbitUnused92DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane92UnusedGenDeadAll : forall i, plane92UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane92UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane92UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane92UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane92UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane92UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane92UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane92UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane92UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane92UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane92UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane92UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane92UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane92UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane92UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane92UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane92UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
