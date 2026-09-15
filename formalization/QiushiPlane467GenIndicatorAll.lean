import QiushiPlane467GenIndicatorBlock0
import QiushiPlane467GenIndicatorBlock1
import QiushiPlane467GenIndicatorBlock2
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane467GenIndicatorAll : forall i, plane467GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane467GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane467GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane467GenIndicatorBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
