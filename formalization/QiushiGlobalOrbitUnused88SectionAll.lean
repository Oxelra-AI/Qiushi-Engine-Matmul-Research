import QiushiGlobalOrbitUnused88SectionBlock0
import QiushiGlobalOrbitUnused88SectionBlock1
import QiushiGlobalOrbitUnused88SectionBlock2
import QiushiGlobalOrbitUnused88SectionBlock3
import QiushiGlobalOrbitUnused88SectionBlock4
import QiushiGlobalOrbitUnused88SectionBlock5
import QiushiGlobalOrbitUnused88SectionBlock6
import QiushiGlobalOrbitUnused88SectionBlock7
import QiushiGlobalOrbitUnused88SectionBlock8
import QiushiGlobalOrbitUnused88SectionBlock9
import QiushiGlobalOrbitUnused88SectionBlock10
import QiushiGlobalOrbitUnused88SectionBlock11
import QiushiGlobalOrbitUnused88SectionBlock12
import QiushiGlobalOrbitUnused88SectionBlock13
import QiushiGlobalOrbitUnused88SectionBlock14
import QiushiGlobalOrbitUnused88SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane88UnusedGenSectionAll : forall i, plane88UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane88UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane88UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane88UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane88UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane88UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane88UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane88UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane88UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane88UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane88UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane88UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane88UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane88UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane88UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane88UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane88UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
