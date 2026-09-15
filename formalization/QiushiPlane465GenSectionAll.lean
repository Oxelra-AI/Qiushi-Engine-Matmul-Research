import QiushiPlane465GenSectionBlock0
import QiushiPlane465GenSectionBlock1
import QiushiPlane465GenSectionBlock2
import QiushiPlane465GenSectionBlock3
import QiushiPlane465GenSectionBlock4
import QiushiPlane465GenSectionBlock5
import QiushiPlane465GenSectionBlock6
import QiushiPlane465GenSectionBlock7
import QiushiPlane465GenSectionBlock8
import QiushiPlane465GenSectionBlock9
import QiushiPlane465GenSectionBlock10
import QiushiPlane465GenSectionBlock11
import QiushiPlane465GenSectionBlock12
import QiushiPlane465GenSectionBlock13
import QiushiPlane465GenSectionBlock14
import QiushiPlane465GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane465GenSectionAll : forall i, plane465GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane465GenSectionBlock0
  | ⟨1, _⟩ => exact plane465GenSectionBlock1
  | ⟨2, _⟩ => exact plane465GenSectionBlock2
  | ⟨3, _⟩ => exact plane465GenSectionBlock3
  | ⟨4, _⟩ => exact plane465GenSectionBlock4
  | ⟨5, _⟩ => exact plane465GenSectionBlock5
  | ⟨6, _⟩ => exact plane465GenSectionBlock6
  | ⟨7, _⟩ => exact plane465GenSectionBlock7
  | ⟨8, _⟩ => exact plane465GenSectionBlock8
  | ⟨9, _⟩ => exact plane465GenSectionBlock9
  | ⟨10, _⟩ => exact plane465GenSectionBlock10
  | ⟨11, _⟩ => exact plane465GenSectionBlock11
  | ⟨12, _⟩ => exact plane465GenSectionBlock12
  | ⟨13, _⟩ => exact plane465GenSectionBlock13
  | ⟨14, _⟩ => exact plane465GenSectionBlock14
  | ⟨15, _⟩ => exact plane465GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
