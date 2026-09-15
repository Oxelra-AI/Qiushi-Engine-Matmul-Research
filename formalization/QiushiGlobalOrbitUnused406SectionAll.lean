import QiushiGlobalOrbitUnused406SectionBlock0
import QiushiGlobalOrbitUnused406SectionBlock1
import QiushiGlobalOrbitUnused406SectionBlock2
import QiushiGlobalOrbitUnused406SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane406UnusedGenSectionAll : forall i, plane406UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane406UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane406UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane406UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane406UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
