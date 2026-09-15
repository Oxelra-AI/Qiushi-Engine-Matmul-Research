import QiushiGlobalOrbitUnused379SectionBlock0
import QiushiGlobalOrbitUnused379SectionBlock1
import QiushiGlobalOrbitUnused379SectionBlock2
import QiushiGlobalOrbitUnused379SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane379UnusedGenSectionAll : forall i, plane379UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane379UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane379UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane379UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane379UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
