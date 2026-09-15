import QiushiPlane315GenSourceBlock0
import QiushiPlane315GenSourceBlock1
import QiushiPlane315GenSourceBlock2
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane315GenSourceAll : forall i, plane315GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane315GenSourceBlock0
  | ⟨1, _⟩ => exact plane315GenSourceBlock1
  | ⟨2, _⟩ => exact plane315GenSourceBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
