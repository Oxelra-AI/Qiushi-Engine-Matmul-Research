import QiushiPlane489GenSourceBlock0
import QiushiPlane489GenSourceBlock1
import QiushiPlane489GenSourceBlock2
import QiushiPlane489GenSourceBlock3
import QiushiPlane489GenSourceBlock4
import QiushiPlane489GenSourceBlock5
import QiushiPlane489GenSourceBlock6
import QiushiPlane489GenSourceBlock7
import QiushiPlane489GenSourceBlock8
import QiushiPlane489GenSourceBlock9
import QiushiPlane489GenSourceBlock10
import QiushiPlane489GenSourceBlock11
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane489GenSourceAll : forall i, plane489GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 12) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane489GenSourceBlock0
  | ⟨1, _⟩ => exact plane489GenSourceBlock1
  | ⟨2, _⟩ => exact plane489GenSourceBlock2
  | ⟨3, _⟩ => exact plane489GenSourceBlock3
  | ⟨4, _⟩ => exact plane489GenSourceBlock4
  | ⟨5, _⟩ => exact plane489GenSourceBlock5
  | ⟨6, _⟩ => exact plane489GenSourceBlock6
  | ⟨7, _⟩ => exact plane489GenSourceBlock7
  | ⟨8, _⟩ => exact plane489GenSourceBlock8
  | ⟨9, _⟩ => exact plane489GenSourceBlock9
  | ⟨10, _⟩ => exact plane489GenSourceBlock10
  | ⟨11, _⟩ => exact plane489GenSourceBlock11
  | ⟨k + 12, h⟩ => omega
end QiushiMatmul
