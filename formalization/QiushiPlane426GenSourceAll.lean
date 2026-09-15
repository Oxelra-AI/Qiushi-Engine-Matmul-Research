import QiushiPlane426GenSourceBlock0
import QiushiPlane426GenSourceBlock1
import QiushiPlane426GenSourceBlock2
import QiushiPlane426GenSourceBlock3
import QiushiPlane426GenSourceBlock4
import QiushiPlane426GenSourceBlock5
import QiushiPlane426GenSourceBlock6
import QiushiPlane426GenSourceBlock7
import QiushiPlane426GenSourceBlock8
import QiushiPlane426GenSourceBlock9
import QiushiPlane426GenSourceBlock10
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane426GenSourceAll : forall i, plane426GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 11) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane426GenSourceBlock0
  | ⟨1, _⟩ => exact plane426GenSourceBlock1
  | ⟨2, _⟩ => exact plane426GenSourceBlock2
  | ⟨3, _⟩ => exact plane426GenSourceBlock3
  | ⟨4, _⟩ => exact plane426GenSourceBlock4
  | ⟨5, _⟩ => exact plane426GenSourceBlock5
  | ⟨6, _⟩ => exact plane426GenSourceBlock6
  | ⟨7, _⟩ => exact plane426GenSourceBlock7
  | ⟨8, _⟩ => exact plane426GenSourceBlock8
  | ⟨9, _⟩ => exact plane426GenSourceBlock9
  | ⟨10, _⟩ => exact plane426GenSourceBlock10
  | ⟨k + 11, h⟩ => omega
end QiushiMatmul
