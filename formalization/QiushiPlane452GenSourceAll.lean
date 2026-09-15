import QiushiPlane452GenSourceBlock0
import QiushiPlane452GenSourceBlock1
import QiushiPlane452GenSourceBlock2
import QiushiPlane452GenSourceBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane452GenSourceAll : forall i, plane452GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane452GenSourceBlock0
  | ⟨1, _⟩ => exact plane452GenSourceBlock1
  | ⟨2, _⟩ => exact plane452GenSourceBlock2
  | ⟨3, _⟩ => exact plane452GenSourceBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
