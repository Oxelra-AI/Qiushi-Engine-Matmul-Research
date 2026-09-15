import QiushiPlane482GenSourceBlock0
import QiushiPlane482GenSourceBlock1
import QiushiPlane482GenSourceBlock2
import QiushiPlane482GenSourceBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane482GenSourceAll : forall i, plane482GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane482GenSourceBlock0
  | ⟨1, _⟩ => exact plane482GenSourceBlock1
  | ⟨2, _⟩ => exact plane482GenSourceBlock2
  | ⟨3, _⟩ => exact plane482GenSourceBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
