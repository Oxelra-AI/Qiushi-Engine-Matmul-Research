import QiushiGlobalOrbitUnused339DeadBlock0
import QiushiGlobalOrbitUnused339DeadBlock1
import QiushiGlobalOrbitUnused339DeadBlock2
import QiushiGlobalOrbitUnused339DeadBlock3
import QiushiGlobalOrbitUnused339DeadBlock4
import QiushiGlobalOrbitUnused339DeadBlock5
import QiushiGlobalOrbitUnused339DeadBlock6
import QiushiGlobalOrbitUnused339DeadBlock7
import QiushiGlobalOrbitUnused339DeadBlock8
import QiushiGlobalOrbitUnused339DeadBlock9
import QiushiGlobalOrbitUnused339DeadBlock10
import QiushiGlobalOrbitUnused339DeadBlock11
import QiushiGlobalOrbitUnused339DeadBlock12
import QiushiGlobalOrbitUnused339DeadBlock13
import QiushiGlobalOrbitUnused339DeadBlock14
import QiushiGlobalOrbitUnused339DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane339UnusedGenDeadAll : forall i, plane339UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane339UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane339UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane339UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane339UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane339UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane339UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane339UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane339UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane339UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane339UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane339UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane339UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane339UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane339UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane339UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane339UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
