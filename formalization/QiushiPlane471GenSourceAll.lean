import QiushiPlane471GenSourceBlock0
import QiushiPlane471GenSourceBlock1
import QiushiPlane471GenSourceBlock2
import QiushiPlane471GenSourceBlock3
import QiushiPlane471GenSourceBlock4
import QiushiPlane471GenSourceBlock5
import QiushiPlane471GenSourceBlock6
import QiushiPlane471GenSourceBlock7
import QiushiPlane471GenSourceBlock8
import QiushiPlane471GenSourceBlock9
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471GenSourceAll : forall i, plane471GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 10) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane471GenSourceBlock0
  | ⟨1, _⟩ => exact plane471GenSourceBlock1
  | ⟨2, _⟩ => exact plane471GenSourceBlock2
  | ⟨3, _⟩ => exact plane471GenSourceBlock3
  | ⟨4, _⟩ => exact plane471GenSourceBlock4
  | ⟨5, _⟩ => exact plane471GenSourceBlock5
  | ⟨6, _⟩ => exact plane471GenSourceBlock6
  | ⟨7, _⟩ => exact plane471GenSourceBlock7
  | ⟨8, _⟩ => exact plane471GenSourceBlock8
  | ⟨9, _⟩ => exact plane471GenSourceBlock9
  | ⟨k + 10, h⟩ => omega
end QiushiMatmul
