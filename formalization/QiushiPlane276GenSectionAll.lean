import QiushiPlane276GenSectionBlock0
import QiushiPlane276GenSectionBlock1
import QiushiPlane276GenSectionBlock2
import QiushiPlane276GenSectionBlock3
import QiushiPlane276GenSectionBlock4
import QiushiPlane276GenSectionBlock5
import QiushiPlane276GenSectionBlock6
import QiushiPlane276GenSectionBlock7
import QiushiPlane276GenSectionBlock8
import QiushiPlane276GenSectionBlock9
import QiushiPlane276GenSectionBlock10
import QiushiPlane276GenSectionBlock11
import QiushiPlane276GenSectionBlock12
import QiushiPlane276GenSectionBlock13
import QiushiPlane276GenSectionBlock14
import QiushiPlane276GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane276GenSectionAll : forall i, plane276GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane276GenSectionBlock0
  | ⟨1, _⟩ => exact plane276GenSectionBlock1
  | ⟨2, _⟩ => exact plane276GenSectionBlock2
  | ⟨3, _⟩ => exact plane276GenSectionBlock3
  | ⟨4, _⟩ => exact plane276GenSectionBlock4
  | ⟨5, _⟩ => exact plane276GenSectionBlock5
  | ⟨6, _⟩ => exact plane276GenSectionBlock6
  | ⟨7, _⟩ => exact plane276GenSectionBlock7
  | ⟨8, _⟩ => exact plane276GenSectionBlock8
  | ⟨9, _⟩ => exact plane276GenSectionBlock9
  | ⟨10, _⟩ => exact plane276GenSectionBlock10
  | ⟨11, _⟩ => exact plane276GenSectionBlock11
  | ⟨12, _⟩ => exact plane276GenSectionBlock12
  | ⟨13, _⟩ => exact plane276GenSectionBlock13
  | ⟨14, _⟩ => exact plane276GenSectionBlock14
  | ⟨15, _⟩ => exact plane276GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
