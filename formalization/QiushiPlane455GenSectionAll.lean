import QiushiPlane455GenSectionBlock0
import QiushiPlane455GenSectionBlock1
import QiushiPlane455GenSectionBlock2
import QiushiPlane455GenSectionBlock3
import QiushiPlane455GenSectionBlock4
import QiushiPlane455GenSectionBlock5
import QiushiPlane455GenSectionBlock6
import QiushiPlane455GenSectionBlock7
import QiushiPlane455GenSectionBlock8
import QiushiPlane455GenSectionBlock9
import QiushiPlane455GenSectionBlock10
import QiushiPlane455GenSectionBlock11
import QiushiPlane455GenSectionBlock12
import QiushiPlane455GenSectionBlock13
import QiushiPlane455GenSectionBlock14
import QiushiPlane455GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane455GenSectionAll : forall i, plane455GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane455GenSectionBlock0
  | ⟨1, _⟩ => exact plane455GenSectionBlock1
  | ⟨2, _⟩ => exact plane455GenSectionBlock2
  | ⟨3, _⟩ => exact plane455GenSectionBlock3
  | ⟨4, _⟩ => exact plane455GenSectionBlock4
  | ⟨5, _⟩ => exact plane455GenSectionBlock5
  | ⟨6, _⟩ => exact plane455GenSectionBlock6
  | ⟨7, _⟩ => exact plane455GenSectionBlock7
  | ⟨8, _⟩ => exact plane455GenSectionBlock8
  | ⟨9, _⟩ => exact plane455GenSectionBlock9
  | ⟨10, _⟩ => exact plane455GenSectionBlock10
  | ⟨11, _⟩ => exact plane455GenSectionBlock11
  | ⟨12, _⟩ => exact plane455GenSectionBlock12
  | ⟨13, _⟩ => exact plane455GenSectionBlock13
  | ⟨14, _⟩ => exact plane455GenSectionBlock14
  | ⟨15, _⟩ => exact plane455GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
