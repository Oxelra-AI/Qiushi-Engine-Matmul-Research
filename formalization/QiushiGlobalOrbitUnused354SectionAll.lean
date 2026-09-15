import QiushiGlobalOrbitUnused354SectionBlock0
import QiushiGlobalOrbitUnused354SectionBlock1
import QiushiGlobalOrbitUnused354SectionBlock2
import QiushiGlobalOrbitUnused354SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane354UnusedGenSectionAll : forall i, plane354UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane354UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane354UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane354UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane354UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
