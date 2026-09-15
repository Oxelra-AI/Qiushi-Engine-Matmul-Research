import QiushiPlane278GenSectionBlock0
import QiushiPlane278GenSectionBlock1
import QiushiPlane278GenSectionBlock2
import QiushiPlane278GenSectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane278GenSectionAll : forall i, plane278GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane278GenSectionBlock0
  | ⟨1, _⟩ => exact plane278GenSectionBlock1
  | ⟨2, _⟩ => exact plane278GenSectionBlock2
  | ⟨3, _⟩ => exact plane278GenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
