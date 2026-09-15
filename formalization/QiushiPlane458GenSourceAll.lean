import QiushiPlane458GenSourceBlock0
import QiushiPlane458GenSourceBlock1
import QiushiPlane458GenSourceBlock2
import QiushiPlane458GenSourceBlock3
import QiushiPlane458GenSourceBlock4
import QiushiPlane458GenSourceBlock5
import QiushiPlane458GenSourceBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane458GenSourceAll : forall i, plane458GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane458GenSourceBlock0
  | ⟨1, _⟩ => exact plane458GenSourceBlock1
  | ⟨2, _⟩ => exact plane458GenSourceBlock2
  | ⟨3, _⟩ => exact plane458GenSourceBlock3
  | ⟨4, _⟩ => exact plane458GenSourceBlock4
  | ⟨5, _⟩ => exact plane458GenSourceBlock5
  | ⟨6, _⟩ => exact plane458GenSourceBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
