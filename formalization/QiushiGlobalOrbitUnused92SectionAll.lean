import QiushiGlobalOrbitUnused92SectionBlock0
import QiushiGlobalOrbitUnused92SectionBlock1
import QiushiGlobalOrbitUnused92SectionBlock2
import QiushiGlobalOrbitUnused92SectionBlock3
import QiushiGlobalOrbitUnused92SectionBlock4
import QiushiGlobalOrbitUnused92SectionBlock5
import QiushiGlobalOrbitUnused92SectionBlock6
import QiushiGlobalOrbitUnused92SectionBlock7
import QiushiGlobalOrbitUnused92SectionBlock8
import QiushiGlobalOrbitUnused92SectionBlock9
import QiushiGlobalOrbitUnused92SectionBlock10
import QiushiGlobalOrbitUnused92SectionBlock11
import QiushiGlobalOrbitUnused92SectionBlock12
import QiushiGlobalOrbitUnused92SectionBlock13
import QiushiGlobalOrbitUnused92SectionBlock14
import QiushiGlobalOrbitUnused92SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane92UnusedGenSectionAll : forall i, plane92UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane92UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane92UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane92UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane92UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane92UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane92UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane92UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane92UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane92UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane92UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane92UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane92UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane92UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane92UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane92UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane92UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
