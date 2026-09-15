import QiushiGlobalOrbitUnused387SectionBlock0
import QiushiGlobalOrbitUnused387SectionBlock1
import QiushiGlobalOrbitUnused387SectionBlock2
import QiushiGlobalOrbitUnused387SectionBlock3
import QiushiGlobalOrbitUnused387SectionBlock4
import QiushiGlobalOrbitUnused387SectionBlock5
import QiushiGlobalOrbitUnused387SectionBlock6
import QiushiGlobalOrbitUnused387SectionBlock7
import QiushiGlobalOrbitUnused387SectionBlock8
import QiushiGlobalOrbitUnused387SectionBlock9
import QiushiGlobalOrbitUnused387SectionBlock10
import QiushiGlobalOrbitUnused387SectionBlock11
import QiushiGlobalOrbitUnused387SectionBlock12
import QiushiGlobalOrbitUnused387SectionBlock13
import QiushiGlobalOrbitUnused387SectionBlock14
import QiushiGlobalOrbitUnused387SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane387UnusedGenSectionAll : forall i, plane387UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane387UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane387UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane387UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane387UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane387UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane387UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane387UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane387UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane387UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane387UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane387UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane387UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane387UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane387UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane387UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane387UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
