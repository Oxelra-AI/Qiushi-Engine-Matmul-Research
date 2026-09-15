import QiushiPlane484GenSectionBlock0
import QiushiPlane484GenSectionBlock1
import QiushiPlane484GenSectionBlock2
import QiushiPlane484GenSectionBlock3
import QiushiPlane484GenSectionBlock4
import QiushiPlane484GenSectionBlock5
import QiushiPlane484GenSectionBlock6
import QiushiPlane484GenSectionBlock7
import QiushiPlane484GenSectionBlock8
import QiushiPlane484GenSectionBlock9
import QiushiPlane484GenSectionBlock10
import QiushiPlane484GenSectionBlock11
import QiushiPlane484GenSectionBlock12
import QiushiPlane484GenSectionBlock13
import QiushiPlane484GenSectionBlock14
import QiushiPlane484GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane484GenSectionAll : forall i, plane484GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane484GenSectionBlock0
  | ⟨1, _⟩ => exact plane484GenSectionBlock1
  | ⟨2, _⟩ => exact plane484GenSectionBlock2
  | ⟨3, _⟩ => exact plane484GenSectionBlock3
  | ⟨4, _⟩ => exact plane484GenSectionBlock4
  | ⟨5, _⟩ => exact plane484GenSectionBlock5
  | ⟨6, _⟩ => exact plane484GenSectionBlock6
  | ⟨7, _⟩ => exact plane484GenSectionBlock7
  | ⟨8, _⟩ => exact plane484GenSectionBlock8
  | ⟨9, _⟩ => exact plane484GenSectionBlock9
  | ⟨10, _⟩ => exact plane484GenSectionBlock10
  | ⟨11, _⟩ => exact plane484GenSectionBlock11
  | ⟨12, _⟩ => exact plane484GenSectionBlock12
  | ⟨13, _⟩ => exact plane484GenSectionBlock13
  | ⟨14, _⟩ => exact plane484GenSectionBlock14
  | ⟨15, _⟩ => exact plane484GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
