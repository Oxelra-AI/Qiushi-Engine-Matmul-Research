import QiushiPlane488GenDeadBlock0
import QiushiPlane488GenDeadBlock1
import QiushiPlane488GenDeadBlock2
import QiushiPlane488GenDeadBlock3
import QiushiPlane488GenDeadBlock4
import QiushiPlane488GenDeadBlock5
import QiushiPlane488GenDeadBlock6
import QiushiPlane488GenDeadBlock7
import QiushiPlane488GenDeadBlock8
import QiushiPlane488GenDeadBlock9
import QiushiPlane488GenDeadBlock10
import QiushiPlane488GenDeadBlock11
import QiushiPlane488GenDeadBlock12
import QiushiPlane488GenDeadBlock13
import QiushiPlane488GenDeadBlock14
import QiushiPlane488GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenDeadAll : forall i, plane488GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488GenDeadBlock0
  | ⟨1, _⟩ => exact plane488GenDeadBlock1
  | ⟨2, _⟩ => exact plane488GenDeadBlock2
  | ⟨3, _⟩ => exact plane488GenDeadBlock3
  | ⟨4, _⟩ => exact plane488GenDeadBlock4
  | ⟨5, _⟩ => exact plane488GenDeadBlock5
  | ⟨6, _⟩ => exact plane488GenDeadBlock6
  | ⟨7, _⟩ => exact plane488GenDeadBlock7
  | ⟨8, _⟩ => exact plane488GenDeadBlock8
  | ⟨9, _⟩ => exact plane488GenDeadBlock9
  | ⟨10, _⟩ => exact plane488GenDeadBlock10
  | ⟨11, _⟩ => exact plane488GenDeadBlock11
  | ⟨12, _⟩ => exact plane488GenDeadBlock12
  | ⟨13, _⟩ => exact plane488GenDeadBlock13
  | ⟨14, _⟩ => exact plane488GenDeadBlock14
  | ⟨15, _⟩ => exact plane488GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
