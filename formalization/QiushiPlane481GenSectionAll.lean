import QiushiPlane481GenSectionBlock0
import QiushiPlane481GenSectionBlock1
import QiushiPlane481GenSectionBlock2
import QiushiPlane481GenSectionBlock3
import QiushiPlane481GenSectionBlock4
import QiushiPlane481GenSectionBlock5
import QiushiPlane481GenSectionBlock6
import QiushiPlane481GenSectionBlock7
import QiushiPlane481GenSectionBlock8
import QiushiPlane481GenSectionBlock9
import QiushiPlane481GenSectionBlock10
import QiushiPlane481GenSectionBlock11
import QiushiPlane481GenSectionBlock12
import QiushiPlane481GenSectionBlock13
import QiushiPlane481GenSectionBlock14
import QiushiPlane481GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenSectionAll : forall i, plane481GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane481GenSectionBlock0
  | ⟨1, _⟩ => exact plane481GenSectionBlock1
  | ⟨2, _⟩ => exact plane481GenSectionBlock2
  | ⟨3, _⟩ => exact plane481GenSectionBlock3
  | ⟨4, _⟩ => exact plane481GenSectionBlock4
  | ⟨5, _⟩ => exact plane481GenSectionBlock5
  | ⟨6, _⟩ => exact plane481GenSectionBlock6
  | ⟨7, _⟩ => exact plane481GenSectionBlock7
  | ⟨8, _⟩ => exact plane481GenSectionBlock8
  | ⟨9, _⟩ => exact plane481GenSectionBlock9
  | ⟨10, _⟩ => exact plane481GenSectionBlock10
  | ⟨11, _⟩ => exact plane481GenSectionBlock11
  | ⟨12, _⟩ => exact plane481GenSectionBlock12
  | ⟨13, _⟩ => exact plane481GenSectionBlock13
  | ⟨14, _⟩ => exact plane481GenSectionBlock14
  | ⟨15, _⟩ => exact plane481GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
