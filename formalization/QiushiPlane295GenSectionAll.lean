import QiushiPlane295GenSectionBlock0
import QiushiPlane295GenSectionBlock1
import QiushiPlane295GenSectionBlock2
import QiushiPlane295GenSectionBlock3
import QiushiPlane295GenSectionBlock4
import QiushiPlane295GenSectionBlock5
import QiushiPlane295GenSectionBlock6
import QiushiPlane295GenSectionBlock7
import QiushiPlane295GenSectionBlock8
import QiushiPlane295GenSectionBlock9
import QiushiPlane295GenSectionBlock10
import QiushiPlane295GenSectionBlock11
import QiushiPlane295GenSectionBlock12
import QiushiPlane295GenSectionBlock13
import QiushiPlane295GenSectionBlock14
import QiushiPlane295GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane295GenSectionAll : forall i, plane295GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane295GenSectionBlock0
  | ⟨1, _⟩ => exact plane295GenSectionBlock1
  | ⟨2, _⟩ => exact plane295GenSectionBlock2
  | ⟨3, _⟩ => exact plane295GenSectionBlock3
  | ⟨4, _⟩ => exact plane295GenSectionBlock4
  | ⟨5, _⟩ => exact plane295GenSectionBlock5
  | ⟨6, _⟩ => exact plane295GenSectionBlock6
  | ⟨7, _⟩ => exact plane295GenSectionBlock7
  | ⟨8, _⟩ => exact plane295GenSectionBlock8
  | ⟨9, _⟩ => exact plane295GenSectionBlock9
  | ⟨10, _⟩ => exact plane295GenSectionBlock10
  | ⟨11, _⟩ => exact plane295GenSectionBlock11
  | ⟨12, _⟩ => exact plane295GenSectionBlock12
  | ⟨13, _⟩ => exact plane295GenSectionBlock13
  | ⟨14, _⟩ => exact plane295GenSectionBlock14
  | ⟨15, _⟩ => exact plane295GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
