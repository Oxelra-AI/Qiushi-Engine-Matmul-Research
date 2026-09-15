import QiushiPlane278GenDeadBlock0
import QiushiPlane278GenDeadBlock1
import QiushiPlane278GenDeadBlock2
import QiushiPlane278GenDeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane278GenDeadAll : forall i, plane278GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane278GenDeadBlock0
  | ⟨1, _⟩ => exact plane278GenDeadBlock1
  | ⟨2, _⟩ => exact plane278GenDeadBlock2
  | ⟨3, _⟩ => exact plane278GenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
