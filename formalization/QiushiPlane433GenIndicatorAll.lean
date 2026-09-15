import QiushiPlane433GenIndicatorBlock0
import QiushiPlane433GenIndicatorBlock1
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane433GenIndicatorAll : forall i, plane433GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 2) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane433GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane433GenIndicatorBlock1
  | ⟨k + 2, h⟩ => omega
end QiushiMatmul
