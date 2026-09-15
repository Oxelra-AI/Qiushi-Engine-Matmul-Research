import QiushiGlobalOrbitUnused382SectionBlock0
import QiushiGlobalOrbitUnused382SectionBlock1
import QiushiGlobalOrbitUnused382SectionBlock2
import QiushiGlobalOrbitUnused382SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane382UnusedGenSectionAll : forall i, plane382UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane382UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane382UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane382UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane382UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
