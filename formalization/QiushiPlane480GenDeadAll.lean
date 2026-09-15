import QiushiPlane480GenDeadBlock0
import QiushiPlane480GenDeadBlock1
import QiushiPlane480GenDeadBlock2
import QiushiPlane480GenDeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane480GenDeadAll : forall i, plane480GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane480GenDeadBlock0
  | ⟨1, _⟩ => exact plane480GenDeadBlock1
  | ⟨2, _⟩ => exact plane480GenDeadBlock2
  | ⟨3, _⟩ => exact plane480GenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
