import QiushiPlane470GenSectionBlock0
import QiushiPlane470GenSectionBlock1
import QiushiPlane470GenSectionBlock2
import QiushiPlane470GenSectionBlock3
import QiushiPlane470GenSectionBlock4
import QiushiPlane470GenSectionBlock5
import QiushiPlane470GenSectionBlock6
import QiushiPlane470GenSectionBlock7
import QiushiPlane470GenSectionBlock8
import QiushiPlane470GenSectionBlock9
import QiushiPlane470GenSectionBlock10
import QiushiPlane470GenSectionBlock11
import QiushiPlane470GenSectionBlock12
import QiushiPlane470GenSectionBlock13
import QiushiPlane470GenSectionBlock14
import QiushiPlane470GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470GenSectionAll : forall i, plane470GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane470GenSectionBlock0
  | ⟨1, _⟩ => exact plane470GenSectionBlock1
  | ⟨2, _⟩ => exact plane470GenSectionBlock2
  | ⟨3, _⟩ => exact plane470GenSectionBlock3
  | ⟨4, _⟩ => exact plane470GenSectionBlock4
  | ⟨5, _⟩ => exact plane470GenSectionBlock5
  | ⟨6, _⟩ => exact plane470GenSectionBlock6
  | ⟨7, _⟩ => exact plane470GenSectionBlock7
  | ⟨8, _⟩ => exact plane470GenSectionBlock8
  | ⟨9, _⟩ => exact plane470GenSectionBlock9
  | ⟨10, _⟩ => exact plane470GenSectionBlock10
  | ⟨11, _⟩ => exact plane470GenSectionBlock11
  | ⟨12, _⟩ => exact plane470GenSectionBlock12
  | ⟨13, _⟩ => exact plane470GenSectionBlock13
  | ⟨14, _⟩ => exact plane470GenSectionBlock14
  | ⟨15, _⟩ => exact plane470GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
