import QiushiPlane454GenSourceBlock0
import QiushiPlane454GenSourceBlock1
import QiushiPlane454GenSourceBlock2
import QiushiPlane454GenSourceBlock3
import QiushiPlane454GenSourceBlock4
import QiushiPlane454GenSourceBlock5
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane454GenSourceAll : forall i, plane454GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 6) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane454GenSourceBlock0
  | ⟨1, _⟩ => exact plane454GenSourceBlock1
  | ⟨2, _⟩ => exact plane454GenSourceBlock2
  | ⟨3, _⟩ => exact plane454GenSourceBlock3
  | ⟨4, _⟩ => exact plane454GenSourceBlock4
  | ⟨5, _⟩ => exact plane454GenSourceBlock5
  | ⟨k + 6, h⟩ => omega
end QiushiMatmul
