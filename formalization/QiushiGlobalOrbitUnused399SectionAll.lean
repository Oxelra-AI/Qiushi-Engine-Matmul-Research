import QiushiGlobalOrbitUnused399SectionBlock0
import QiushiGlobalOrbitUnused399SectionBlock1
import QiushiGlobalOrbitUnused399SectionBlock2
import QiushiGlobalOrbitUnused399SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane399UnusedGenSectionAll : forall i, plane399UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane399UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane399UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane399UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane399UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
