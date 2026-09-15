import QiushiPlane476GenIndicatorBlock0
import QiushiPlane476GenIndicatorBlock1
import QiushiPlane476GenIndicatorBlock2
import QiushiPlane476GenIndicatorBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane476GenIndicatorAll : forall i, plane476GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane476GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane476GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane476GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane476GenIndicatorBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
