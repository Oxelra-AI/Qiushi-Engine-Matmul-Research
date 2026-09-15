import QiushiPlane473GenSourceBlock0
import QiushiPlane473GenSourceBlock1
import QiushiPlane473GenSourceBlock2
import QiushiPlane473GenSourceBlock3
import QiushiPlane473GenSourceBlock4
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane473GenSourceAll : forall i, plane473GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 5) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane473GenSourceBlock0
  | ⟨1, _⟩ => exact plane473GenSourceBlock1
  | ⟨2, _⟩ => exact plane473GenSourceBlock2
  | ⟨3, _⟩ => exact plane473GenSourceBlock3
  | ⟨4, _⟩ => exact plane473GenSourceBlock4
  | ⟨k + 5, h⟩ => omega
end QiushiMatmul
