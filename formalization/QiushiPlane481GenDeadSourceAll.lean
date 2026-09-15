import QiushiPlane481GenDeadSourceBlock0
import QiushiPlane481GenDeadSourceBlock1
import QiushiPlane481GenDeadSourceBlock2
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenDeadSourceAll : forall i, plane481GenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane481GenDeadSourceBlock0
  | ⟨1, _⟩ => exact plane481GenDeadSourceBlock1
  | ⟨2, _⟩ => exact plane481GenDeadSourceBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
