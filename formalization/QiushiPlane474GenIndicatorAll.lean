import QiushiPlane474GenIndicatorBlock0
import QiushiPlane474GenIndicatorBlock1
import QiushiPlane474GenIndicatorBlock2
import QiushiPlane474GenIndicatorBlock3
import QiushiPlane474GenIndicatorBlock4
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenIndicatorAll : forall i, plane474GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 5) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane474GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane474GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane474GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane474GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane474GenIndicatorBlock4
  | ⟨k + 5, h⟩ => omega
end QiushiMatmul
