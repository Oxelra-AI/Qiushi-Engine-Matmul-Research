import QiushiGlobalOrbitUnused372SectionBlock0
import QiushiGlobalOrbitUnused372SectionBlock1
import QiushiGlobalOrbitUnused372SectionBlock2
import QiushiGlobalOrbitUnused372SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane372UnusedGenSectionAll : forall i, plane372UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane372UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane372UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane372UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane372UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
