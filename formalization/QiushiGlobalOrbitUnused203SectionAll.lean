import QiushiGlobalOrbitUnused203SectionBlock0
import QiushiGlobalOrbitUnused203SectionBlock1
import QiushiGlobalOrbitUnused203SectionBlock2
import QiushiGlobalOrbitUnused203SectionBlock3
import QiushiGlobalOrbitUnused203SectionBlock4
import QiushiGlobalOrbitUnused203SectionBlock5
import QiushiGlobalOrbitUnused203SectionBlock6
import QiushiGlobalOrbitUnused203SectionBlock7
import QiushiGlobalOrbitUnused203SectionBlock8
import QiushiGlobalOrbitUnused203SectionBlock9
import QiushiGlobalOrbitUnused203SectionBlock10
import QiushiGlobalOrbitUnused203SectionBlock11
import QiushiGlobalOrbitUnused203SectionBlock12
import QiushiGlobalOrbitUnused203SectionBlock13
import QiushiGlobalOrbitUnused203SectionBlock14
import QiushiGlobalOrbitUnused203SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane203UnusedGenSectionAll : forall i, plane203UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane203UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane203UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane203UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane203UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane203UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane203UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane203UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane203UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane203UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane203UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane203UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane203UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane203UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane203UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane203UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane203UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
