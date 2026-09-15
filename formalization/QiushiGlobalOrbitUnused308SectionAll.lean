import QiushiGlobalOrbitUnused308SectionBlock0
import QiushiGlobalOrbitUnused308SectionBlock1
import QiushiGlobalOrbitUnused308SectionBlock2
import QiushiGlobalOrbitUnused308SectionBlock3
import QiushiGlobalOrbitUnused308SectionBlock4
import QiushiGlobalOrbitUnused308SectionBlock5
import QiushiGlobalOrbitUnused308SectionBlock6
import QiushiGlobalOrbitUnused308SectionBlock7
import QiushiGlobalOrbitUnused308SectionBlock8
import QiushiGlobalOrbitUnused308SectionBlock9
import QiushiGlobalOrbitUnused308SectionBlock10
import QiushiGlobalOrbitUnused308SectionBlock11
import QiushiGlobalOrbitUnused308SectionBlock12
import QiushiGlobalOrbitUnused308SectionBlock13
import QiushiGlobalOrbitUnused308SectionBlock14
import QiushiGlobalOrbitUnused308SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane308UnusedGenSectionAll : forall i, plane308UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane308UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane308UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane308UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane308UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane308UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane308UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane308UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane308UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane308UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane308UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane308UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane308UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane308UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane308UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane308UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane308UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
