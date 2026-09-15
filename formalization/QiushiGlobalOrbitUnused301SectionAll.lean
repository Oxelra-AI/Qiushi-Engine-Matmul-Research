import QiushiGlobalOrbitUnused301SectionBlock0
import QiushiGlobalOrbitUnused301SectionBlock1
import QiushiGlobalOrbitUnused301SectionBlock2
import QiushiGlobalOrbitUnused301SectionBlock3
import QiushiGlobalOrbitUnused301SectionBlock4
import QiushiGlobalOrbitUnused301SectionBlock5
import QiushiGlobalOrbitUnused301SectionBlock6
import QiushiGlobalOrbitUnused301SectionBlock7
import QiushiGlobalOrbitUnused301SectionBlock8
import QiushiGlobalOrbitUnused301SectionBlock9
import QiushiGlobalOrbitUnused301SectionBlock10
import QiushiGlobalOrbitUnused301SectionBlock11
import QiushiGlobalOrbitUnused301SectionBlock12
import QiushiGlobalOrbitUnused301SectionBlock13
import QiushiGlobalOrbitUnused301SectionBlock14
import QiushiGlobalOrbitUnused301SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane301UnusedGenSectionAll : forall i, plane301UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane301UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane301UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane301UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane301UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane301UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane301UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane301UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane301UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane301UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane301UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane301UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane301UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane301UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane301UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane301UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane301UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
