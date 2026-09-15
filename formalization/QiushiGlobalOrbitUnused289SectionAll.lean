import QiushiGlobalOrbitUnused289SectionBlock0
import QiushiGlobalOrbitUnused289SectionBlock1
import QiushiGlobalOrbitUnused289SectionBlock2
import QiushiGlobalOrbitUnused289SectionBlock3
import QiushiGlobalOrbitUnused289SectionBlock4
import QiushiGlobalOrbitUnused289SectionBlock5
import QiushiGlobalOrbitUnused289SectionBlock6
import QiushiGlobalOrbitUnused289SectionBlock7
import QiushiGlobalOrbitUnused289SectionBlock8
import QiushiGlobalOrbitUnused289SectionBlock9
import QiushiGlobalOrbitUnused289SectionBlock10
import QiushiGlobalOrbitUnused289SectionBlock11
import QiushiGlobalOrbitUnused289SectionBlock12
import QiushiGlobalOrbitUnused289SectionBlock13
import QiushiGlobalOrbitUnused289SectionBlock14
import QiushiGlobalOrbitUnused289SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane289UnusedGenSectionAll : forall i, plane289UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane289UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane289UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane289UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane289UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane289UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane289UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane289UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane289UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane289UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane289UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane289UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane289UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane289UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane289UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane289UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane289UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
