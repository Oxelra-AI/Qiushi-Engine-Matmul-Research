import QiushiGlobalOrbitUnused305DeadBlock0
import QiushiGlobalOrbitUnused305DeadBlock1
import QiushiGlobalOrbitUnused305DeadBlock2
import QiushiGlobalOrbitUnused305DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane305UnusedGenDeadAll : forall i, plane305UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane305UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane305UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane305UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane305UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
