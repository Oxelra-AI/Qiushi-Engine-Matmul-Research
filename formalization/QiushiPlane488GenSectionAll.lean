import QiushiPlane488GenSectionBlock0
import QiushiPlane488GenSectionBlock1
import QiushiPlane488GenSectionBlock2
import QiushiPlane488GenSectionBlock3
import QiushiPlane488GenSectionBlock4
import QiushiPlane488GenSectionBlock5
import QiushiPlane488GenSectionBlock6
import QiushiPlane488GenSectionBlock7
import QiushiPlane488GenSectionBlock8
import QiushiPlane488GenSectionBlock9
import QiushiPlane488GenSectionBlock10
import QiushiPlane488GenSectionBlock11
import QiushiPlane488GenSectionBlock12
import QiushiPlane488GenSectionBlock13
import QiushiPlane488GenSectionBlock14
import QiushiPlane488GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenSectionAll : forall i, plane488GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488GenSectionBlock0
  | ⟨1, _⟩ => exact plane488GenSectionBlock1
  | ⟨2, _⟩ => exact plane488GenSectionBlock2
  | ⟨3, _⟩ => exact plane488GenSectionBlock3
  | ⟨4, _⟩ => exact plane488GenSectionBlock4
  | ⟨5, _⟩ => exact plane488GenSectionBlock5
  | ⟨6, _⟩ => exact plane488GenSectionBlock6
  | ⟨7, _⟩ => exact plane488GenSectionBlock7
  | ⟨8, _⟩ => exact plane488GenSectionBlock8
  | ⟨9, _⟩ => exact plane488GenSectionBlock9
  | ⟨10, _⟩ => exact plane488GenSectionBlock10
  | ⟨11, _⟩ => exact plane488GenSectionBlock11
  | ⟨12, _⟩ => exact plane488GenSectionBlock12
  | ⟨13, _⟩ => exact plane488GenSectionBlock13
  | ⟨14, _⟩ => exact plane488GenSectionBlock14
  | ⟨15, _⟩ => exact plane488GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
