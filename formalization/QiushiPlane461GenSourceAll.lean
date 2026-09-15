import QiushiPlane461GenSourceBlock0
import QiushiPlane461GenSourceBlock1
import QiushiPlane461GenSourceBlock2
import QiushiPlane461GenSourceBlock3
import QiushiPlane461GenSourceBlock4
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane461GenSourceAll : forall i, plane461GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 5) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane461GenSourceBlock0
  | ⟨1, _⟩ => exact plane461GenSourceBlock1
  | ⟨2, _⟩ => exact plane461GenSourceBlock2
  | ⟨3, _⟩ => exact plane461GenSourceBlock3
  | ⟨4, _⟩ => exact plane461GenSourceBlock4
  | ⟨k + 5, h⟩ => omega
end QiushiMatmul
