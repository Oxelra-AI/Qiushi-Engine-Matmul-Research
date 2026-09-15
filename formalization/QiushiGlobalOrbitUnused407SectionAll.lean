import QiushiGlobalOrbitUnused407SectionBlock0
import QiushiGlobalOrbitUnused407SectionBlock1
import QiushiGlobalOrbitUnused407SectionBlock2
import QiushiGlobalOrbitUnused407SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane407UnusedGenSectionAll : forall i, plane407UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane407UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane407UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane407UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane407UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
