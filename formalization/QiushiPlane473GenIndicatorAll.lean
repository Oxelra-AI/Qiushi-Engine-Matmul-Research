import QiushiPlane473GenIndicatorBlock0
import QiushiPlane473GenIndicatorBlock1
import QiushiPlane473GenIndicatorBlock2
import QiushiPlane473GenIndicatorBlock3
import QiushiPlane473GenIndicatorBlock4
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane473GenIndicatorAll : forall i, plane473GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 5) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane473GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane473GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane473GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane473GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane473GenIndicatorBlock4
  | ⟨k + 5, h⟩ => omega
end QiushiMatmul
