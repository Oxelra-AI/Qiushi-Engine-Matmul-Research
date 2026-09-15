import QiushiPlane464GenSourceBlock0
import QiushiPlane464GenSourceBlock1
import QiushiPlane464GenSourceBlock2
import QiushiPlane464GenSourceBlock3
import QiushiPlane464GenSourceBlock4
import QiushiPlane464GenSourceBlock5
import QiushiPlane464GenSourceBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane464GenSourceAll : forall i, plane464GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane464GenSourceBlock0
  | ⟨1, _⟩ => exact plane464GenSourceBlock1
  | ⟨2, _⟩ => exact plane464GenSourceBlock2
  | ⟨3, _⟩ => exact plane464GenSourceBlock3
  | ⟨4, _⟩ => exact plane464GenSourceBlock4
  | ⟨5, _⟩ => exact plane464GenSourceBlock5
  | ⟨6, _⟩ => exact plane464GenSourceBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
