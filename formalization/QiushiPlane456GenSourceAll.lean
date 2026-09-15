import QiushiPlane456GenSourceBlock0
import QiushiPlane456GenSourceBlock1
import QiushiPlane456GenSourceBlock2
import QiushiPlane456GenSourceBlock3
import QiushiPlane456GenSourceBlock4
import QiushiPlane456GenSourceBlock5
import QiushiPlane456GenSourceBlock6
import QiushiPlane456GenSourceBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456GenSourceAll : forall i, plane456GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane456GenSourceBlock0
  | ⟨1, _⟩ => exact plane456GenSourceBlock1
  | ⟨2, _⟩ => exact plane456GenSourceBlock2
  | ⟨3, _⟩ => exact plane456GenSourceBlock3
  | ⟨4, _⟩ => exact plane456GenSourceBlock4
  | ⟨5, _⟩ => exact plane456GenSourceBlock5
  | ⟨6, _⟩ => exact plane456GenSourceBlock6
  | ⟨7, _⟩ => exact plane456GenSourceBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
