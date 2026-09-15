import QiushiPlane336GenDeadBlock0
import QiushiPlane336GenDeadBlock1
import QiushiPlane336GenDeadBlock2
import QiushiPlane336GenDeadBlock3
import QiushiPlane336GenDeadBlock4
import QiushiPlane336GenDeadBlock5
import QiushiPlane336GenDeadBlock6
import QiushiPlane336GenDeadBlock7
import QiushiPlane336GenDeadBlock8
import QiushiPlane336GenDeadBlock9
import QiushiPlane336GenDeadBlock10
import QiushiPlane336GenDeadBlock11
import QiushiPlane336GenDeadBlock12
import QiushiPlane336GenDeadBlock13
import QiushiPlane336GenDeadBlock14
import QiushiPlane336GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane336GenDeadAll : forall i, plane336GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane336GenDeadBlock0
  | ⟨1, _⟩ => exact plane336GenDeadBlock1
  | ⟨2, _⟩ => exact plane336GenDeadBlock2
  | ⟨3, _⟩ => exact plane336GenDeadBlock3
  | ⟨4, _⟩ => exact plane336GenDeadBlock4
  | ⟨5, _⟩ => exact plane336GenDeadBlock5
  | ⟨6, _⟩ => exact plane336GenDeadBlock6
  | ⟨7, _⟩ => exact plane336GenDeadBlock7
  | ⟨8, _⟩ => exact plane336GenDeadBlock8
  | ⟨9, _⟩ => exact plane336GenDeadBlock9
  | ⟨10, _⟩ => exact plane336GenDeadBlock10
  | ⟨11, _⟩ => exact plane336GenDeadBlock11
  | ⟨12, _⟩ => exact plane336GenDeadBlock12
  | ⟨13, _⟩ => exact plane336GenDeadBlock13
  | ⟨14, _⟩ => exact plane336GenDeadBlock14
  | ⟨15, _⟩ => exact plane336GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
