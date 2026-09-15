import QiushiGlobalOrbitUnused376DeadBlock0
import QiushiGlobalOrbitUnused376DeadBlock1
import QiushiGlobalOrbitUnused376DeadBlock2
import QiushiGlobalOrbitUnused376DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane376UnusedGenDeadAll : forall i, plane376UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane376UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane376UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane376UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane376UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
