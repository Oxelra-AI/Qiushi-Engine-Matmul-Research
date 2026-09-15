import QiushiPlane468GenSourceBlock0
import QiushiPlane468GenSourceBlock1
import QiushiPlane468GenSourceBlock2
import QiushiPlane468GenSourceBlock3
import QiushiPlane468GenSourceBlock4
import QiushiPlane468GenSourceBlock5
import QiushiPlane468GenSourceBlock6
import QiushiPlane468GenSourceBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane468GenSourceAll : forall i, plane468GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane468GenSourceBlock0
  | ⟨1, _⟩ => exact plane468GenSourceBlock1
  | ⟨2, _⟩ => exact plane468GenSourceBlock2
  | ⟨3, _⟩ => exact plane468GenSourceBlock3
  | ⟨4, _⟩ => exact plane468GenSourceBlock4
  | ⟨5, _⟩ => exact plane468GenSourceBlock5
  | ⟨6, _⟩ => exact plane468GenSourceBlock6
  | ⟨7, _⟩ => exact plane468GenSourceBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
