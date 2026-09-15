import QiushiPlane434GenSectionBlock0
import QiushiPlane434GenSectionBlock1
import QiushiPlane434GenSectionBlock2
import QiushiPlane434GenSectionBlock3
import QiushiPlane434GenSectionBlock4
import QiushiPlane434GenSectionBlock5
import QiushiPlane434GenSectionBlock6
import QiushiPlane434GenSectionBlock7
import QiushiPlane434GenSectionBlock8
import QiushiPlane434GenSectionBlock9
import QiushiPlane434GenSectionBlock10
import QiushiPlane434GenSectionBlock11
import QiushiPlane434GenSectionBlock12
import QiushiPlane434GenSectionBlock13
import QiushiPlane434GenSectionBlock14
import QiushiPlane434GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane434GenSectionAll : forall i, plane434GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane434GenSectionBlock0
  | ⟨1, _⟩ => exact plane434GenSectionBlock1
  | ⟨2, _⟩ => exact plane434GenSectionBlock2
  | ⟨3, _⟩ => exact plane434GenSectionBlock3
  | ⟨4, _⟩ => exact plane434GenSectionBlock4
  | ⟨5, _⟩ => exact plane434GenSectionBlock5
  | ⟨6, _⟩ => exact plane434GenSectionBlock6
  | ⟨7, _⟩ => exact plane434GenSectionBlock7
  | ⟨8, _⟩ => exact plane434GenSectionBlock8
  | ⟨9, _⟩ => exact plane434GenSectionBlock9
  | ⟨10, _⟩ => exact plane434GenSectionBlock10
  | ⟨11, _⟩ => exact plane434GenSectionBlock11
  | ⟨12, _⟩ => exact plane434GenSectionBlock12
  | ⟨13, _⟩ => exact plane434GenSectionBlock13
  | ⟨14, _⟩ => exact plane434GenSectionBlock14
  | ⟨15, _⟩ => exact plane434GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
