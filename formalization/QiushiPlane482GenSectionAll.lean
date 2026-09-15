import QiushiPlane482GenSectionBlock0
import QiushiPlane482GenSectionBlock1
import QiushiPlane482GenSectionBlock2
import QiushiPlane482GenSectionBlock3
import QiushiPlane482GenSectionBlock4
import QiushiPlane482GenSectionBlock5
import QiushiPlane482GenSectionBlock6
import QiushiPlane482GenSectionBlock7
import QiushiPlane482GenSectionBlock8
import QiushiPlane482GenSectionBlock9
import QiushiPlane482GenSectionBlock10
import QiushiPlane482GenSectionBlock11
import QiushiPlane482GenSectionBlock12
import QiushiPlane482GenSectionBlock13
import QiushiPlane482GenSectionBlock14
import QiushiPlane482GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane482GenSectionAll : forall i, plane482GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane482GenSectionBlock0
  | ⟨1, _⟩ => exact plane482GenSectionBlock1
  | ⟨2, _⟩ => exact plane482GenSectionBlock2
  | ⟨3, _⟩ => exact plane482GenSectionBlock3
  | ⟨4, _⟩ => exact plane482GenSectionBlock4
  | ⟨5, _⟩ => exact plane482GenSectionBlock5
  | ⟨6, _⟩ => exact plane482GenSectionBlock6
  | ⟨7, _⟩ => exact plane482GenSectionBlock7
  | ⟨8, _⟩ => exact plane482GenSectionBlock8
  | ⟨9, _⟩ => exact plane482GenSectionBlock9
  | ⟨10, _⟩ => exact plane482GenSectionBlock10
  | ⟨11, _⟩ => exact plane482GenSectionBlock11
  | ⟨12, _⟩ => exact plane482GenSectionBlock12
  | ⟨13, _⟩ => exact plane482GenSectionBlock13
  | ⟨14, _⟩ => exact plane482GenSectionBlock14
  | ⟨15, _⟩ => exact plane482GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
