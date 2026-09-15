import QiushiGlobalOrbitUnused394SectionBlock0
import QiushiGlobalOrbitUnused394SectionBlock1
import QiushiGlobalOrbitUnused394SectionBlock2
import QiushiGlobalOrbitUnused394SectionBlock3
import QiushiGlobalOrbitUnused394SectionBlock4
import QiushiGlobalOrbitUnused394SectionBlock5
import QiushiGlobalOrbitUnused394SectionBlock6
import QiushiGlobalOrbitUnused394SectionBlock7
import QiushiGlobalOrbitUnused394SectionBlock8
import QiushiGlobalOrbitUnused394SectionBlock9
import QiushiGlobalOrbitUnused394SectionBlock10
import QiushiGlobalOrbitUnused394SectionBlock11
import QiushiGlobalOrbitUnused394SectionBlock12
import QiushiGlobalOrbitUnused394SectionBlock13
import QiushiGlobalOrbitUnused394SectionBlock14
import QiushiGlobalOrbitUnused394SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane394UnusedGenSectionAll : forall i, plane394UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane394UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane394UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane394UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane394UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane394UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane394UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane394UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane394UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane394UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane394UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane394UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane394UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane394UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane394UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane394UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane394UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
