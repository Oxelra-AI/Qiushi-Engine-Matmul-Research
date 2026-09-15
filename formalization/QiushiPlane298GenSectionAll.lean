import QiushiPlane298GenSectionBlock0
import QiushiPlane298GenSectionBlock1
import QiushiPlane298GenSectionBlock2
import QiushiPlane298GenSectionBlock3
import QiushiPlane298GenSectionBlock4
import QiushiPlane298GenSectionBlock5
import QiushiPlane298GenSectionBlock6
import QiushiPlane298GenSectionBlock7
import QiushiPlane298GenSectionBlock8
import QiushiPlane298GenSectionBlock9
import QiushiPlane298GenSectionBlock10
import QiushiPlane298GenSectionBlock11
import QiushiPlane298GenSectionBlock12
import QiushiPlane298GenSectionBlock13
import QiushiPlane298GenSectionBlock14
import QiushiPlane298GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane298GenSectionAll : forall i, plane298GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane298GenSectionBlock0
  | ⟨1, _⟩ => exact plane298GenSectionBlock1
  | ⟨2, _⟩ => exact plane298GenSectionBlock2
  | ⟨3, _⟩ => exact plane298GenSectionBlock3
  | ⟨4, _⟩ => exact plane298GenSectionBlock4
  | ⟨5, _⟩ => exact plane298GenSectionBlock5
  | ⟨6, _⟩ => exact plane298GenSectionBlock6
  | ⟨7, _⟩ => exact plane298GenSectionBlock7
  | ⟨8, _⟩ => exact plane298GenSectionBlock8
  | ⟨9, _⟩ => exact plane298GenSectionBlock9
  | ⟨10, _⟩ => exact plane298GenSectionBlock10
  | ⟨11, _⟩ => exact plane298GenSectionBlock11
  | ⟨12, _⟩ => exact plane298GenSectionBlock12
  | ⟨13, _⟩ => exact plane298GenSectionBlock13
  | ⟨14, _⟩ => exact plane298GenSectionBlock14
  | ⟨15, _⟩ => exact plane298GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
