import QiushiGlobalOrbitUnused398SectionBlock0
import QiushiGlobalOrbitUnused398SectionBlock1
import QiushiGlobalOrbitUnused398SectionBlock2
import QiushiGlobalOrbitUnused398SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane398UnusedGenSectionAll : forall i, plane398UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane398UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane398UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane398UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane398UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
