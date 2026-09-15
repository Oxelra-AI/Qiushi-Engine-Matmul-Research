import QiushiPlane485GenDeadSourceBlock0
import QiushiPlane485GenDeadSourceBlock1
import QiushiPlane485GenDeadSourceBlock2
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenDeadSourceAll : forall i, plane485GenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485GenDeadSourceBlock0
  | ⟨1, _⟩ => exact plane485GenDeadSourceBlock1
  | ⟨2, _⟩ => exact plane485GenDeadSourceBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
