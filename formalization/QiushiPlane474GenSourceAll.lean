import QiushiPlane474GenSourceBlock0
import QiushiPlane474GenSourceBlock1
import QiushiPlane474GenSourceBlock2
import QiushiPlane474GenSourceBlock3
import QiushiPlane474GenSourceBlock4
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenSourceAll : forall i, plane474GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 5) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane474GenSourceBlock0
  | ⟨1, _⟩ => exact plane474GenSourceBlock1
  | ⟨2, _⟩ => exact plane474GenSourceBlock2
  | ⟨3, _⟩ => exact plane474GenSourceBlock3
  | ⟨4, _⟩ => exact plane474GenSourceBlock4
  | ⟨k + 5, h⟩ => omega
end QiushiMatmul
