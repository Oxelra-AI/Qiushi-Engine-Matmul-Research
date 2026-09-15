import QiushiPlane255GenSectionBlock0
import QiushiPlane255GenSectionBlock1
import QiushiPlane255GenSectionBlock2
import QiushiPlane255GenSectionBlock3
import QiushiPlane255GenSectionBlock4
import QiushiPlane255GenSectionBlock5
import QiushiPlane255GenSectionBlock6
import QiushiPlane255GenSectionBlock7
import QiushiPlane255GenSectionBlock8
import QiushiPlane255GenSectionBlock9
import QiushiPlane255GenSectionBlock10
import QiushiPlane255GenSectionBlock11
import QiushiPlane255GenSectionBlock12
import QiushiPlane255GenSectionBlock13
import QiushiPlane255GenSectionBlock14
import QiushiPlane255GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane255GenSectionAll : forall i, plane255GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane255GenSectionBlock0
  | ⟨1, _⟩ => exact plane255GenSectionBlock1
  | ⟨2, _⟩ => exact plane255GenSectionBlock2
  | ⟨3, _⟩ => exact plane255GenSectionBlock3
  | ⟨4, _⟩ => exact plane255GenSectionBlock4
  | ⟨5, _⟩ => exact plane255GenSectionBlock5
  | ⟨6, _⟩ => exact plane255GenSectionBlock6
  | ⟨7, _⟩ => exact plane255GenSectionBlock7
  | ⟨8, _⟩ => exact plane255GenSectionBlock8
  | ⟨9, _⟩ => exact plane255GenSectionBlock9
  | ⟨10, _⟩ => exact plane255GenSectionBlock10
  | ⟨11, _⟩ => exact plane255GenSectionBlock11
  | ⟨12, _⟩ => exact plane255GenSectionBlock12
  | ⟨13, _⟩ => exact plane255GenSectionBlock13
  | ⟨14, _⟩ => exact plane255GenSectionBlock14
  | ⟨15, _⟩ => exact plane255GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
