import QiushiPlane480GenSectionBlock0
import QiushiPlane480GenSectionBlock1
import QiushiPlane480GenSectionBlock2
import QiushiPlane480GenSectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane480GenSectionAll : forall i, plane480GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane480GenSectionBlock0
  | ⟨1, _⟩ => exact plane480GenSectionBlock1
  | ⟨2, _⟩ => exact plane480GenSectionBlock2
  | ⟨3, _⟩ => exact plane480GenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
