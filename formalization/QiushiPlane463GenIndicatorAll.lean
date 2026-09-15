import QiushiPlane463GenIndicatorBlock0
import QiushiPlane463GenIndicatorBlock1
import QiushiPlane463GenIndicatorBlock2
import QiushiPlane463GenIndicatorBlock3
import QiushiPlane463GenIndicatorBlock4
import QiushiPlane463GenIndicatorBlock5
import QiushiPlane463GenIndicatorBlock6
import QiushiPlane463GenIndicatorBlock7
import QiushiPlane463GenIndicatorBlock8
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463GenIndicatorAll : forall i, plane463GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 9) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane463GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane463GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane463GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane463GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane463GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane463GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane463GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane463GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane463GenIndicatorBlock8
  | ⟨k + 9, h⟩ => omega
end QiushiMatmul
