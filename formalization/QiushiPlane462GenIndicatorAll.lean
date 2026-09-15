import QiushiPlane462GenIndicatorBlock0
import QiushiPlane462GenIndicatorBlock1
import QiushiPlane462GenIndicatorBlock2
import QiushiPlane462GenIndicatorBlock3
import QiushiPlane462GenIndicatorBlock4
import QiushiPlane462GenIndicatorBlock5
import QiushiPlane462GenIndicatorBlock6
import QiushiPlane462GenIndicatorBlock7
import QiushiPlane462GenIndicatorBlock8
import QiushiPlane462GenIndicatorBlock9
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane462GenIndicatorAll : forall i, plane462GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 10) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane462GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane462GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane462GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane462GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane462GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane462GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane462GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane462GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane462GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane462GenIndicatorBlock9
  | ⟨k + 10, h⟩ => omega
end QiushiMatmul
