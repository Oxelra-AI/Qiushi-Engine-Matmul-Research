import QiushiPlane439GenDeadBlock0
import QiushiPlane439GenDeadBlock1
import QiushiPlane439GenDeadBlock2
import QiushiPlane439GenDeadBlock3
import QiushiPlane439GenDeadBlock4
import QiushiPlane439GenDeadBlock5
import QiushiPlane439GenDeadBlock6
import QiushiPlane439GenDeadBlock7
import QiushiPlane439GenDeadBlock8
import QiushiPlane439GenDeadBlock9
import QiushiPlane439GenDeadBlock10
import QiushiPlane439GenDeadBlock11
import QiushiPlane439GenDeadBlock12
import QiushiPlane439GenDeadBlock13
import QiushiPlane439GenDeadBlock14
import QiushiPlane439GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane439GenDeadAll : forall i, plane439GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane439GenDeadBlock0
  | ⟨1, _⟩ => exact plane439GenDeadBlock1
  | ⟨2, _⟩ => exact plane439GenDeadBlock2
  | ⟨3, _⟩ => exact plane439GenDeadBlock3
  | ⟨4, _⟩ => exact plane439GenDeadBlock4
  | ⟨5, _⟩ => exact plane439GenDeadBlock5
  | ⟨6, _⟩ => exact plane439GenDeadBlock6
  | ⟨7, _⟩ => exact plane439GenDeadBlock7
  | ⟨8, _⟩ => exact plane439GenDeadBlock8
  | ⟨9, _⟩ => exact plane439GenDeadBlock9
  | ⟨10, _⟩ => exact plane439GenDeadBlock10
  | ⟨11, _⟩ => exact plane439GenDeadBlock11
  | ⟨12, _⟩ => exact plane439GenDeadBlock12
  | ⟨13, _⟩ => exact plane439GenDeadBlock13
  | ⟨14, _⟩ => exact plane439GenDeadBlock14
  | ⟨15, _⟩ => exact plane439GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
