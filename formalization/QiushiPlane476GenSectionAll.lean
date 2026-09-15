import QiushiPlane476GenSectionBlock0
import QiushiPlane476GenSectionBlock1
import QiushiPlane476GenSectionBlock2
import QiushiPlane476GenSectionBlock3
import QiushiPlane476GenSectionBlock4
import QiushiPlane476GenSectionBlock5
import QiushiPlane476GenSectionBlock6
import QiushiPlane476GenSectionBlock7
import QiushiPlane476GenSectionBlock8
import QiushiPlane476GenSectionBlock9
import QiushiPlane476GenSectionBlock10
import QiushiPlane476GenSectionBlock11
import QiushiPlane476GenSectionBlock12
import QiushiPlane476GenSectionBlock13
import QiushiPlane476GenSectionBlock14
import QiushiPlane476GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane476GenSectionAll : forall i, plane476GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane476GenSectionBlock0
  | ⟨1, _⟩ => exact plane476GenSectionBlock1
  | ⟨2, _⟩ => exact plane476GenSectionBlock2
  | ⟨3, _⟩ => exact plane476GenSectionBlock3
  | ⟨4, _⟩ => exact plane476GenSectionBlock4
  | ⟨5, _⟩ => exact plane476GenSectionBlock5
  | ⟨6, _⟩ => exact plane476GenSectionBlock6
  | ⟨7, _⟩ => exact plane476GenSectionBlock7
  | ⟨8, _⟩ => exact plane476GenSectionBlock8
  | ⟨9, _⟩ => exact plane476GenSectionBlock9
  | ⟨10, _⟩ => exact plane476GenSectionBlock10
  | ⟨11, _⟩ => exact plane476GenSectionBlock11
  | ⟨12, _⟩ => exact plane476GenSectionBlock12
  | ⟨13, _⟩ => exact plane476GenSectionBlock13
  | ⟨14, _⟩ => exact plane476GenSectionBlock14
  | ⟨15, _⟩ => exact plane476GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
