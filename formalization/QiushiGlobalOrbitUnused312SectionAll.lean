import QiushiGlobalOrbitUnused312SectionBlock0
import QiushiGlobalOrbitUnused312SectionBlock1
import QiushiGlobalOrbitUnused312SectionBlock2
import QiushiGlobalOrbitUnused312SectionBlock3
import QiushiGlobalOrbitUnused312SectionBlock4
import QiushiGlobalOrbitUnused312SectionBlock5
import QiushiGlobalOrbitUnused312SectionBlock6
import QiushiGlobalOrbitUnused312SectionBlock7
import QiushiGlobalOrbitUnused312SectionBlock8
import QiushiGlobalOrbitUnused312SectionBlock9
import QiushiGlobalOrbitUnused312SectionBlock10
import QiushiGlobalOrbitUnused312SectionBlock11
import QiushiGlobalOrbitUnused312SectionBlock12
import QiushiGlobalOrbitUnused312SectionBlock13
import QiushiGlobalOrbitUnused312SectionBlock14
import QiushiGlobalOrbitUnused312SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane312UnusedGenSectionAll : forall i, plane312UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane312UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane312UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane312UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane312UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane312UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane312UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane312UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane312UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane312UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane312UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane312UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane312UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane312UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane312UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane312UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane312UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
