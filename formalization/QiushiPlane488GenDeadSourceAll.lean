import QiushiPlane488GenDeadSourceBlock0
import QiushiPlane488GenDeadSourceBlock1
import QiushiPlane488GenDeadSourceBlock2
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenDeadSourceAll : forall i, plane488GenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488GenDeadSourceBlock0
  | ⟨1, _⟩ => exact plane488GenDeadSourceBlock1
  | ⟨2, _⟩ => exact plane488GenDeadSourceBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
