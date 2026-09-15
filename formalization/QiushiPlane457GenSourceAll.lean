import QiushiPlane457GenSourceBlock0
import QiushiPlane457GenSourceBlock1
import QiushiPlane457GenSourceBlock2
import QiushiPlane457GenSourceBlock3
import QiushiPlane457GenSourceBlock4
import QiushiPlane457GenSourceBlock5
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane457GenSourceAll : forall i, plane457GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 6) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane457GenSourceBlock0
  | ⟨1, _⟩ => exact plane457GenSourceBlock1
  | ⟨2, _⟩ => exact plane457GenSourceBlock2
  | ⟨3, _⟩ => exact plane457GenSourceBlock3
  | ⟨4, _⟩ => exact plane457GenSourceBlock4
  | ⟨5, _⟩ => exact plane457GenSourceBlock5
  | ⟨k + 6, h⟩ => omega
end QiushiMatmul
