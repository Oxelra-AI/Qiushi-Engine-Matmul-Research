import QiushiPlane270GenSectionBlock0
import QiushiPlane270GenSectionBlock1
import QiushiPlane270GenSectionBlock2
import QiushiPlane270GenSectionBlock3
import QiushiPlane270GenSectionBlock4
import QiushiPlane270GenSectionBlock5
import QiushiPlane270GenSectionBlock6
import QiushiPlane270GenSectionBlock7
import QiushiPlane270GenSectionBlock8
import QiushiPlane270GenSectionBlock9
import QiushiPlane270GenSectionBlock10
import QiushiPlane270GenSectionBlock11
import QiushiPlane270GenSectionBlock12
import QiushiPlane270GenSectionBlock13
import QiushiPlane270GenSectionBlock14
import QiushiPlane270GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane270GenSectionAll : forall i, plane270GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane270GenSectionBlock0
  | ⟨1, _⟩ => exact plane270GenSectionBlock1
  | ⟨2, _⟩ => exact plane270GenSectionBlock2
  | ⟨3, _⟩ => exact plane270GenSectionBlock3
  | ⟨4, _⟩ => exact plane270GenSectionBlock4
  | ⟨5, _⟩ => exact plane270GenSectionBlock5
  | ⟨6, _⟩ => exact plane270GenSectionBlock6
  | ⟨7, _⟩ => exact plane270GenSectionBlock7
  | ⟨8, _⟩ => exact plane270GenSectionBlock8
  | ⟨9, _⟩ => exact plane270GenSectionBlock9
  | ⟨10, _⟩ => exact plane270GenSectionBlock10
  | ⟨11, _⟩ => exact plane270GenSectionBlock11
  | ⟨12, _⟩ => exact plane270GenSectionBlock12
  | ⟨13, _⟩ => exact plane270GenSectionBlock13
  | ⟨14, _⟩ => exact plane270GenSectionBlock14
  | ⟨15, _⟩ => exact plane270GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
