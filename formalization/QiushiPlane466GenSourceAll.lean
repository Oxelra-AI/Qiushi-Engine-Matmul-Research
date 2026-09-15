import QiushiPlane466GenSourceBlock0
import QiushiPlane466GenSourceBlock1
import QiushiPlane466GenSourceBlock2
import QiushiPlane466GenSourceBlock3
import QiushiPlane466GenSourceBlock4
import QiushiPlane466GenSourceBlock5
import QiushiPlane466GenSourceBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenSourceAll : forall i, plane466GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane466GenSourceBlock0
  | ⟨1, _⟩ => exact plane466GenSourceBlock1
  | ⟨2, _⟩ => exact plane466GenSourceBlock2
  | ⟨3, _⟩ => exact plane466GenSourceBlock3
  | ⟨4, _⟩ => exact plane466GenSourceBlock4
  | ⟨5, _⟩ => exact plane466GenSourceBlock5
  | ⟨6, _⟩ => exact plane466GenSourceBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
