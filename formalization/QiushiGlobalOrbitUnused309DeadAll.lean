import QiushiGlobalOrbitUnused309DeadBlock0
import QiushiGlobalOrbitUnused309DeadBlock1
import QiushiGlobalOrbitUnused309DeadBlock2
import QiushiGlobalOrbitUnused309DeadBlock3
import QiushiGlobalOrbitUnused309DeadBlock4
import QiushiGlobalOrbitUnused309DeadBlock5
import QiushiGlobalOrbitUnused309DeadBlock6
import QiushiGlobalOrbitUnused309DeadBlock7
import QiushiGlobalOrbitUnused309DeadBlock8
import QiushiGlobalOrbitUnused309DeadBlock9
import QiushiGlobalOrbitUnused309DeadBlock10
import QiushiGlobalOrbitUnused309DeadBlock11
import QiushiGlobalOrbitUnused309DeadBlock12
import QiushiGlobalOrbitUnused309DeadBlock13
import QiushiGlobalOrbitUnused309DeadBlock14
import QiushiGlobalOrbitUnused309DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane309UnusedGenDeadAll : forall i, plane309UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane309UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane309UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane309UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane309UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane309UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane309UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane309UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane309UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane309UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane309UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane309UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane309UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane309UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane309UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane309UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane309UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
