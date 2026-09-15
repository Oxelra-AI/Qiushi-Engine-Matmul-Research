import QiushiGlobalOrbitUnused339SectionBlock0
import QiushiGlobalOrbitUnused339SectionBlock1
import QiushiGlobalOrbitUnused339SectionBlock2
import QiushiGlobalOrbitUnused339SectionBlock3
import QiushiGlobalOrbitUnused339SectionBlock4
import QiushiGlobalOrbitUnused339SectionBlock5
import QiushiGlobalOrbitUnused339SectionBlock6
import QiushiGlobalOrbitUnused339SectionBlock7
import QiushiGlobalOrbitUnused339SectionBlock8
import QiushiGlobalOrbitUnused339SectionBlock9
import QiushiGlobalOrbitUnused339SectionBlock10
import QiushiGlobalOrbitUnused339SectionBlock11
import QiushiGlobalOrbitUnused339SectionBlock12
import QiushiGlobalOrbitUnused339SectionBlock13
import QiushiGlobalOrbitUnused339SectionBlock14
import QiushiGlobalOrbitUnused339SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane339UnusedGenSectionAll : forall i, plane339UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane339UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane339UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane339UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane339UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane339UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane339UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane339UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane339UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane339UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane339UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane339UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane339UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane339UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane339UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane339UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane339UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
