import QiushiPlane455GenSourceBlock0
import QiushiPlane455GenSourceBlock1
import QiushiPlane455GenSourceBlock2
import QiushiPlane455GenSourceBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane455GenSourceAll : forall i, plane455GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane455GenSourceBlock0
  | ⟨1, _⟩ => exact plane455GenSourceBlock1
  | ⟨2, _⟩ => exact plane455GenSourceBlock2
  | ⟨3, _⟩ => exact plane455GenSourceBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
