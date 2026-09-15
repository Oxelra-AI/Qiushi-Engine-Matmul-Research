import QiushiPlane427GenIndicatorBlock0
import QiushiPlane427GenIndicatorBlock1
import QiushiPlane427GenIndicatorBlock2
import QiushiPlane427GenIndicatorBlock3
import QiushiPlane427GenIndicatorBlock4
import QiushiPlane427GenIndicatorBlock5
import QiushiPlane427GenIndicatorBlock6
import QiushiPlane427GenIndicatorBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane427GenIndicatorAll : forall i, plane427GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane427GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane427GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane427GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane427GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane427GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane427GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane427GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane427GenIndicatorBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
