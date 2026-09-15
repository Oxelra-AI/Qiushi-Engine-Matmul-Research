import QiushiGlobalOrbitUnused309SectionBlock0
import QiushiGlobalOrbitUnused309SectionBlock1
import QiushiGlobalOrbitUnused309SectionBlock2
import QiushiGlobalOrbitUnused309SectionBlock3
import QiushiGlobalOrbitUnused309SectionBlock4
import QiushiGlobalOrbitUnused309SectionBlock5
import QiushiGlobalOrbitUnused309SectionBlock6
import QiushiGlobalOrbitUnused309SectionBlock7
import QiushiGlobalOrbitUnused309SectionBlock8
import QiushiGlobalOrbitUnused309SectionBlock9
import QiushiGlobalOrbitUnused309SectionBlock10
import QiushiGlobalOrbitUnused309SectionBlock11
import QiushiGlobalOrbitUnused309SectionBlock12
import QiushiGlobalOrbitUnused309SectionBlock13
import QiushiGlobalOrbitUnused309SectionBlock14
import QiushiGlobalOrbitUnused309SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane309UnusedGenSectionAll : forall i, plane309UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane309UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane309UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane309UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane309UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane309UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane309UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane309UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane309UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane309UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane309UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane309UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane309UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane309UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane309UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane309UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane309UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
