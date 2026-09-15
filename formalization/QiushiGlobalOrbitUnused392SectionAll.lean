import QiushiGlobalOrbitUnused392SectionBlock0
import QiushiGlobalOrbitUnused392SectionBlock1
import QiushiGlobalOrbitUnused392SectionBlock2
import QiushiGlobalOrbitUnused392SectionBlock3
import QiushiGlobalOrbitUnused392SectionBlock4
import QiushiGlobalOrbitUnused392SectionBlock5
import QiushiGlobalOrbitUnused392SectionBlock6
import QiushiGlobalOrbitUnused392SectionBlock7
import QiushiGlobalOrbitUnused392SectionBlock8
import QiushiGlobalOrbitUnused392SectionBlock9
import QiushiGlobalOrbitUnused392SectionBlock10
import QiushiGlobalOrbitUnused392SectionBlock11
import QiushiGlobalOrbitUnused392SectionBlock12
import QiushiGlobalOrbitUnused392SectionBlock13
import QiushiGlobalOrbitUnused392SectionBlock14
import QiushiGlobalOrbitUnused392SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane392UnusedGenSectionAll : forall i, plane392UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane392UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane392UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane392UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane392UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane392UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane392UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane392UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane392UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane392UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane392UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane392UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane392UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane392UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane392UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane392UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane392UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
