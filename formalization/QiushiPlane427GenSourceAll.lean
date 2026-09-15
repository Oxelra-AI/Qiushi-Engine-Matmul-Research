import QiushiPlane427GenSourceBlock0
import QiushiPlane427GenSourceBlock1
import QiushiPlane427GenSourceBlock2
import QiushiPlane427GenSourceBlock3
import QiushiPlane427GenSourceBlock4
import QiushiPlane427GenSourceBlock5
import QiushiPlane427GenSourceBlock6
import QiushiPlane427GenSourceBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane427GenSourceAll : forall i, plane427GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane427GenSourceBlock0
  | ⟨1, _⟩ => exact plane427GenSourceBlock1
  | ⟨2, _⟩ => exact plane427GenSourceBlock2
  | ⟨3, _⟩ => exact plane427GenSourceBlock3
  | ⟨4, _⟩ => exact plane427GenSourceBlock4
  | ⟨5, _⟩ => exact plane427GenSourceBlock5
  | ⟨6, _⟩ => exact plane427GenSourceBlock6
  | ⟨7, _⟩ => exact plane427GenSourceBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
