import QiushiPlane486GenSourceBlock0
import QiushiPlane486GenSourceBlock1
import QiushiPlane486GenSourceBlock2
import QiushiPlane486GenSourceBlock3
import QiushiPlane486GenSourceBlock4
import QiushiPlane486GenSourceBlock5
import QiushiPlane486GenSourceBlock6
import QiushiPlane486GenSourceBlock7
import QiushiPlane486GenSourceBlock8
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane486GenSourceAll : forall i, plane486GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 9) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane486GenSourceBlock0
  | ⟨1, _⟩ => exact plane486GenSourceBlock1
  | ⟨2, _⟩ => exact plane486GenSourceBlock2
  | ⟨3, _⟩ => exact plane486GenSourceBlock3
  | ⟨4, _⟩ => exact plane486GenSourceBlock4
  | ⟨5, _⟩ => exact plane486GenSourceBlock5
  | ⟨6, _⟩ => exact plane486GenSourceBlock6
  | ⟨7, _⟩ => exact plane486GenSourceBlock7
  | ⟨8, _⟩ => exact plane486GenSourceBlock8
  | ⟨k + 9, h⟩ => omega
end QiushiMatmul
