import QiushiPlane462GenSourceBlock0
import QiushiPlane462GenSourceBlock1
import QiushiPlane462GenSourceBlock2
import QiushiPlane462GenSourceBlock3
import QiushiPlane462GenSourceBlock4
import QiushiPlane462GenSourceBlock5
import QiushiPlane462GenSourceBlock6
import QiushiPlane462GenSourceBlock7
import QiushiPlane462GenSourceBlock8
import QiushiPlane462GenSourceBlock9
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane462GenSourceAll : forall i, plane462GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 10) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane462GenSourceBlock0
  | ⟨1, _⟩ => exact plane462GenSourceBlock1
  | ⟨2, _⟩ => exact plane462GenSourceBlock2
  | ⟨3, _⟩ => exact plane462GenSourceBlock3
  | ⟨4, _⟩ => exact plane462GenSourceBlock4
  | ⟨5, _⟩ => exact plane462GenSourceBlock5
  | ⟨6, _⟩ => exact plane462GenSourceBlock6
  | ⟨7, _⟩ => exact plane462GenSourceBlock7
  | ⟨8, _⟩ => exact plane462GenSourceBlock8
  | ⟨9, _⟩ => exact plane462GenSourceBlock9
  | ⟨k + 10, h⟩ => omega
end QiushiMatmul
