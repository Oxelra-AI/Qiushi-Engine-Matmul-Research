import QiushiPlane425GenSourceBlock0
import QiushiPlane425GenSourceBlock1
import QiushiPlane425GenSourceBlock2
import QiushiPlane425GenSourceBlock3
import QiushiPlane425GenSourceBlock4
import QiushiPlane425GenSourceBlock5
import QiushiPlane425GenSourceBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane425GenSourceAll : forall i, plane425GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane425GenSourceBlock0
  | ⟨1, _⟩ => exact plane425GenSourceBlock1
  | ⟨2, _⟩ => exact plane425GenSourceBlock2
  | ⟨3, _⟩ => exact plane425GenSourceBlock3
  | ⟨4, _⟩ => exact plane425GenSourceBlock4
  | ⟨5, _⟩ => exact plane425GenSourceBlock5
  | ⟨6, _⟩ => exact plane425GenSourceBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
