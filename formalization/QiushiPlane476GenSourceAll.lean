import QiushiPlane476GenSourceBlock0
import QiushiPlane476GenSourceBlock1
import QiushiPlane476GenSourceBlock2
import QiushiPlane476GenSourceBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane476GenSourceAll : forall i, plane476GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane476GenSourceBlock0
  | ⟨1, _⟩ => exact plane476GenSourceBlock1
  | ⟨2, _⟩ => exact plane476GenSourceBlock2
  | ⟨3, _⟩ => exact plane476GenSourceBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
