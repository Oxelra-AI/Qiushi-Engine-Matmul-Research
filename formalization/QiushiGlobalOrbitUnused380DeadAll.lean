import QiushiGlobalOrbitUnused380DeadBlock0
import QiushiGlobalOrbitUnused380DeadBlock1
import QiushiGlobalOrbitUnused380DeadBlock2
import QiushiGlobalOrbitUnused380DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane380UnusedGenDeadAll : forall i, plane380UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane380UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane380UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane380UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane380UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
