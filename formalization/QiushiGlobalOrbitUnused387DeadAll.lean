import QiushiGlobalOrbitUnused387DeadBlock0
import QiushiGlobalOrbitUnused387DeadBlock1
import QiushiGlobalOrbitUnused387DeadBlock2
import QiushiGlobalOrbitUnused387DeadBlock3
import QiushiGlobalOrbitUnused387DeadBlock4
import QiushiGlobalOrbitUnused387DeadBlock5
import QiushiGlobalOrbitUnused387DeadBlock6
import QiushiGlobalOrbitUnused387DeadBlock7
import QiushiGlobalOrbitUnused387DeadBlock8
import QiushiGlobalOrbitUnused387DeadBlock9
import QiushiGlobalOrbitUnused387DeadBlock10
import QiushiGlobalOrbitUnused387DeadBlock11
import QiushiGlobalOrbitUnused387DeadBlock12
import QiushiGlobalOrbitUnused387DeadBlock13
import QiushiGlobalOrbitUnused387DeadBlock14
import QiushiGlobalOrbitUnused387DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane387UnusedGenDeadAll : forall i, plane387UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane387UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane387UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane387UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane387UnusedGenDeadBlock3
  | ⟨4, _⟩ => exact plane387UnusedGenDeadBlock4
  | ⟨5, _⟩ => exact plane387UnusedGenDeadBlock5
  | ⟨6, _⟩ => exact plane387UnusedGenDeadBlock6
  | ⟨7, _⟩ => exact plane387UnusedGenDeadBlock7
  | ⟨8, _⟩ => exact plane387UnusedGenDeadBlock8
  | ⟨9, _⟩ => exact plane387UnusedGenDeadBlock9
  | ⟨10, _⟩ => exact plane387UnusedGenDeadBlock10
  | ⟨11, _⟩ => exact plane387UnusedGenDeadBlock11
  | ⟨12, _⟩ => exact plane387UnusedGenDeadBlock12
  | ⟨13, _⟩ => exact plane387UnusedGenDeadBlock13
  | ⟨14, _⟩ => exact plane387UnusedGenDeadBlock14
  | ⟨15, _⟩ => exact plane387UnusedGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
