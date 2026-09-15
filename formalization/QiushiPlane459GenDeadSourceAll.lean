import QiushiPlane459GenDeadSourceBlock0
import QiushiPlane459GenDeadSourceBlock1
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane459GenDeadSourceAll : forall i, plane459GenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 2) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane459GenDeadSourceBlock0
  | ⟨1, _⟩ => exact plane459GenDeadSourceBlock1
  | ⟨k + 2, h⟩ => omega
end QiushiMatmul
