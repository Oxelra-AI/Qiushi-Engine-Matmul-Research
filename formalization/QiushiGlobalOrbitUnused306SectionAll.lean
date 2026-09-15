import QiushiGlobalOrbitUnused306SectionBlock0
import QiushiGlobalOrbitUnused306SectionBlock1
import QiushiGlobalOrbitUnused306SectionBlock2
import QiushiGlobalOrbitUnused306SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane306UnusedGenSectionAll : forall i, plane306UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane306UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane306UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane306UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane306UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
