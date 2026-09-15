import QiushiPlane439GenSectionBlock0
import QiushiPlane439GenSectionBlock1
import QiushiPlane439GenSectionBlock2
import QiushiPlane439GenSectionBlock3
import QiushiPlane439GenSectionBlock4
import QiushiPlane439GenSectionBlock5
import QiushiPlane439GenSectionBlock6
import QiushiPlane439GenSectionBlock7
import QiushiPlane439GenSectionBlock8
import QiushiPlane439GenSectionBlock9
import QiushiPlane439GenSectionBlock10
import QiushiPlane439GenSectionBlock11
import QiushiPlane439GenSectionBlock12
import QiushiPlane439GenSectionBlock13
import QiushiPlane439GenSectionBlock14
import QiushiPlane439GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane439GenSectionAll : forall i, plane439GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane439GenSectionBlock0
  | ⟨1, _⟩ => exact plane439GenSectionBlock1
  | ⟨2, _⟩ => exact plane439GenSectionBlock2
  | ⟨3, _⟩ => exact plane439GenSectionBlock3
  | ⟨4, _⟩ => exact plane439GenSectionBlock4
  | ⟨5, _⟩ => exact plane439GenSectionBlock5
  | ⟨6, _⟩ => exact plane439GenSectionBlock6
  | ⟨7, _⟩ => exact plane439GenSectionBlock7
  | ⟨8, _⟩ => exact plane439GenSectionBlock8
  | ⟨9, _⟩ => exact plane439GenSectionBlock9
  | ⟨10, _⟩ => exact plane439GenSectionBlock10
  | ⟨11, _⟩ => exact plane439GenSectionBlock11
  | ⟨12, _⟩ => exact plane439GenSectionBlock12
  | ⟨13, _⟩ => exact plane439GenSectionBlock13
  | ⟨14, _⟩ => exact plane439GenSectionBlock14
  | ⟨15, _⟩ => exact plane439GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
