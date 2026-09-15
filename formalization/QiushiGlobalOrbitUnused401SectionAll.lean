import QiushiGlobalOrbitUnused401SectionBlock0
import QiushiGlobalOrbitUnused401SectionBlock1
import QiushiGlobalOrbitUnused401SectionBlock2
import QiushiGlobalOrbitUnused401SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane401UnusedGenSectionAll : forall i, plane401UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane401UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane401UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane401UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane401UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
