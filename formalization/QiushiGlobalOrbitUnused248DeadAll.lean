import QiushiGlobalOrbitUnused248DeadBlock0
import QiushiGlobalOrbitUnused248DeadBlock1
import QiushiGlobalOrbitUnused248DeadBlock2
import QiushiGlobalOrbitUnused248DeadBlock3
import QiushiGlobalOrbitUnused248DeadBlock4
import QiushiGlobalOrbitUnused248DeadBlock5
import QiushiGlobalOrbitUnused248DeadBlock6
import QiushiGlobalOrbitUnused248DeadBlock7
import QiushiGlobalOrbitUnused248DeadBlock8
import QiushiGlobalOrbitUnused248DeadBlock9
import QiushiGlobalOrbitUnused248DeadBlock10
import QiushiGlobalOrbitUnused248DeadBlock11
import QiushiGlobalOrbitUnused248DeadBlock12
import QiushiGlobalOrbitUnused248DeadBlock13
import QiushiGlobalOrbitUnused248DeadBlock14
import QiushiGlobalOrbitUnused248DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane248UnusedGenDeadAll : forall i, plane248UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane248UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane248UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane248UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane248UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane248UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane248UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane248UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane248UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane248UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane248UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane248UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane248UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane248UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane248UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane248UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane248UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
