import QiushiPlane480GenSourceBlock0
import QiushiPlane480GenSourceBlock1
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane480GenSourceAll : forall i, plane480GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 2) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane480GenSourceBlock0
  | ⟨1, _⟩ => exact plane480GenSourceBlock1
  | ⟨k + 2, h⟩ => omega
end QiushiMatmul
