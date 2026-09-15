import QiushiGlobalOrbitUnused304DeadBlock0
import QiushiGlobalOrbitUnused304DeadBlock1
import QiushiGlobalOrbitUnused304DeadBlock2
import QiushiGlobalOrbitUnused304DeadBlock3
import QiushiGlobalOrbitUnused304DeadBlock4
import QiushiGlobalOrbitUnused304DeadBlock5
import QiushiGlobalOrbitUnused304DeadBlock6
import QiushiGlobalOrbitUnused304DeadBlock7
import QiushiGlobalOrbitUnused304DeadBlock8
import QiushiGlobalOrbitUnused304DeadBlock9
import QiushiGlobalOrbitUnused304DeadBlock10
import QiushiGlobalOrbitUnused304DeadBlock11
import QiushiGlobalOrbitUnused304DeadBlock12
import QiushiGlobalOrbitUnused304DeadBlock13
import QiushiGlobalOrbitUnused304DeadBlock14
import QiushiGlobalOrbitUnused304DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane304UnusedGenDeadAll : forall i, plane304UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane304UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane304UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane304UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane304UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane304UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane304UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane304UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane304UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane304UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane304UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane304UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane304UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane304UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane304UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane304UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane304UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
