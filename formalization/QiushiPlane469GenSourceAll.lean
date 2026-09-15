import QiushiPlane469GenSourceBlock0
import QiushiPlane469GenSourceBlock1
import QiushiPlane469GenSourceBlock2
import QiushiPlane469GenSourceBlock3
import QiushiPlane469GenSourceBlock4
import QiushiPlane469GenSourceBlock5
import QiushiPlane469GenSourceBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane469GenSourceAll : forall i, plane469GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane469GenSourceBlock0
  | ⟨1, _⟩ => exact plane469GenSourceBlock1
  | ⟨2, _⟩ => exact plane469GenSourceBlock2
  | ⟨3, _⟩ => exact plane469GenSourceBlock3
  | ⟨4, _⟩ => exact plane469GenSourceBlock4
  | ⟨5, _⟩ => exact plane469GenSourceBlock5
  | ⟨6, _⟩ => exact plane469GenSourceBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
