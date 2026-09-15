import QiushiGlobalOrbitUnused302SectionBlock0
import QiushiGlobalOrbitUnused302SectionBlock1
import QiushiGlobalOrbitUnused302SectionBlock2
import QiushiGlobalOrbitUnused302SectionBlock3
import QiushiGlobalOrbitUnused302SectionBlock4
import QiushiGlobalOrbitUnused302SectionBlock5
import QiushiGlobalOrbitUnused302SectionBlock6
import QiushiGlobalOrbitUnused302SectionBlock7
import QiushiGlobalOrbitUnused302SectionBlock8
import QiushiGlobalOrbitUnused302SectionBlock9
import QiushiGlobalOrbitUnused302SectionBlock10
import QiushiGlobalOrbitUnused302SectionBlock11
import QiushiGlobalOrbitUnused302SectionBlock12
import QiushiGlobalOrbitUnused302SectionBlock13
import QiushiGlobalOrbitUnused302SectionBlock14
import QiushiGlobalOrbitUnused302SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane302UnusedGenSectionAll : forall i, plane302UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane302UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane302UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane302UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane302UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane302UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane302UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane302UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane302UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane302UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane302UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane302UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane302UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane302UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane302UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane302UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane302UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
