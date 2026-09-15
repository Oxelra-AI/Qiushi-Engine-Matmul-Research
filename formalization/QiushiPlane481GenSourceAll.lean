import QiushiPlane481GenSourceBlock0
import QiushiPlane481GenSourceBlock1
import QiushiPlane481GenSourceBlock2
import QiushiPlane481GenSourceBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenSourceAll : forall i, plane481GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane481GenSourceBlock0
  | ⟨1, _⟩ => exact plane481GenSourceBlock1
  | ⟨2, _⟩ => exact plane481GenSourceBlock2
  | ⟨3, _⟩ => exact plane481GenSourceBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
