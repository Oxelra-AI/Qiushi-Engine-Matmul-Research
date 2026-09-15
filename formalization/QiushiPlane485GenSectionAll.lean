import QiushiPlane485GenSectionBlock0
import QiushiPlane485GenSectionBlock1
import QiushiPlane485GenSectionBlock2
import QiushiPlane485GenSectionBlock3
import QiushiPlane485GenSectionBlock4
import QiushiPlane485GenSectionBlock5
import QiushiPlane485GenSectionBlock6
import QiushiPlane485GenSectionBlock7
import QiushiPlane485GenSectionBlock8
import QiushiPlane485GenSectionBlock9
import QiushiPlane485GenSectionBlock10
import QiushiPlane485GenSectionBlock11
import QiushiPlane485GenSectionBlock12
import QiushiPlane485GenSectionBlock13
import QiushiPlane485GenSectionBlock14
import QiushiPlane485GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenSectionAll : forall i, plane485GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485GenSectionBlock0
  | ⟨1, _⟩ => exact plane485GenSectionBlock1
  | ⟨2, _⟩ => exact plane485GenSectionBlock2
  | ⟨3, _⟩ => exact plane485GenSectionBlock3
  | ⟨4, _⟩ => exact plane485GenSectionBlock4
  | ⟨5, _⟩ => exact plane485GenSectionBlock5
  | ⟨6, _⟩ => exact plane485GenSectionBlock6
  | ⟨7, _⟩ => exact plane485GenSectionBlock7
  | ⟨8, _⟩ => exact plane485GenSectionBlock8
  | ⟨9, _⟩ => exact plane485GenSectionBlock9
  | ⟨10, _⟩ => exact plane485GenSectionBlock10
  | ⟨11, _⟩ => exact plane485GenSectionBlock11
  | ⟨12, _⟩ => exact plane485GenSectionBlock12
  | ⟨13, _⟩ => exact plane485GenSectionBlock13
  | ⟨14, _⟩ => exact plane485GenSectionBlock14
  | ⟨15, _⟩ => exact plane485GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
