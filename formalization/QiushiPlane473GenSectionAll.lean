import QiushiPlane473GenSectionBlock0
import QiushiPlane473GenSectionBlock1
import QiushiPlane473GenSectionBlock2
import QiushiPlane473GenSectionBlock3
import QiushiPlane473GenSectionBlock4
import QiushiPlane473GenSectionBlock5
import QiushiPlane473GenSectionBlock6
import QiushiPlane473GenSectionBlock7
import QiushiPlane473GenSectionBlock8
import QiushiPlane473GenSectionBlock9
import QiushiPlane473GenSectionBlock10
import QiushiPlane473GenSectionBlock11
import QiushiPlane473GenSectionBlock12
import QiushiPlane473GenSectionBlock13
import QiushiPlane473GenSectionBlock14
import QiushiPlane473GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane473GenSectionAll : forall i, plane473GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane473GenSectionBlock0
  | ⟨1, _⟩ => exact plane473GenSectionBlock1
  | ⟨2, _⟩ => exact plane473GenSectionBlock2
  | ⟨3, _⟩ => exact plane473GenSectionBlock3
  | ⟨4, _⟩ => exact plane473GenSectionBlock4
  | ⟨5, _⟩ => exact plane473GenSectionBlock5
  | ⟨6, _⟩ => exact plane473GenSectionBlock6
  | ⟨7, _⟩ => exact plane473GenSectionBlock7
  | ⟨8, _⟩ => exact plane473GenSectionBlock8
  | ⟨9, _⟩ => exact plane473GenSectionBlock9
  | ⟨10, _⟩ => exact plane473GenSectionBlock10
  | ⟨11, _⟩ => exact plane473GenSectionBlock11
  | ⟨12, _⟩ => exact plane473GenSectionBlock12
  | ⟨13, _⟩ => exact plane473GenSectionBlock13
  | ⟨14, _⟩ => exact plane473GenSectionBlock14
  | ⟨15, _⟩ => exact plane473GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
