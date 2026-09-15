import QiushiPlane470GenIndicatorBlock0
import QiushiPlane470GenIndicatorBlock1
import QiushiPlane470GenIndicatorBlock2
import QiushiPlane470GenIndicatorBlock3
import QiushiPlane470GenIndicatorBlock4
import QiushiPlane470GenIndicatorBlock5
import QiushiPlane470GenIndicatorBlock6
import QiushiPlane470GenIndicatorBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470GenIndicatorAll : forall i, plane470GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane470GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane470GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane470GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane470GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane470GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane470GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane470GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane470GenIndicatorBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
