import QiushiGlobalOrbitUnused240SectionBlock0
import QiushiGlobalOrbitUnused240SectionBlock1
import QiushiGlobalOrbitUnused240SectionBlock2
import QiushiGlobalOrbitUnused240SectionBlock3
import QiushiGlobalOrbitUnused240SectionBlock4
import QiushiGlobalOrbitUnused240SectionBlock5
import QiushiGlobalOrbitUnused240SectionBlock6
import QiushiGlobalOrbitUnused240SectionBlock7
import QiushiGlobalOrbitUnused240SectionBlock8
import QiushiGlobalOrbitUnused240SectionBlock9
import QiushiGlobalOrbitUnused240SectionBlock10
import QiushiGlobalOrbitUnused240SectionBlock11
import QiushiGlobalOrbitUnused240SectionBlock12
import QiushiGlobalOrbitUnused240SectionBlock13
import QiushiGlobalOrbitUnused240SectionBlock14
import QiushiGlobalOrbitUnused240SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane240UnusedGenSectionAll : forall i, plane240UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane240UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane240UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane240UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane240UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane240UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane240UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane240UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane240UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane240UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane240UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane240UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane240UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane240UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane240UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane240UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane240UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
