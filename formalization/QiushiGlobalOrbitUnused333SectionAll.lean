import QiushiGlobalOrbitUnused333SectionBlock0
import QiushiGlobalOrbitUnused333SectionBlock1
import QiushiGlobalOrbitUnused333SectionBlock2
import QiushiGlobalOrbitUnused333SectionBlock3
import QiushiGlobalOrbitUnused333SectionBlock4
import QiushiGlobalOrbitUnused333SectionBlock5
import QiushiGlobalOrbitUnused333SectionBlock6
import QiushiGlobalOrbitUnused333SectionBlock7
import QiushiGlobalOrbitUnused333SectionBlock8
import QiushiGlobalOrbitUnused333SectionBlock9
import QiushiGlobalOrbitUnused333SectionBlock10
import QiushiGlobalOrbitUnused333SectionBlock11
import QiushiGlobalOrbitUnused333SectionBlock12
import QiushiGlobalOrbitUnused333SectionBlock13
import QiushiGlobalOrbitUnused333SectionBlock14
import QiushiGlobalOrbitUnused333SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane333UnusedGenSectionAll : forall i, plane333UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane333UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane333UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane333UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane333UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane333UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane333UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane333UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane333UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane333UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane333UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane333UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane333UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane333UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane333UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane333UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane333UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
