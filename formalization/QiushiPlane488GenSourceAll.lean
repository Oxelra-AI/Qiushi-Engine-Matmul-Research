import QiushiPlane488GenSourceBlock0
import QiushiPlane488GenSourceBlock1
import QiushiPlane488GenSourceBlock2
import QiushiPlane488GenSourceBlock3
import QiushiPlane488GenSourceBlock4
import QiushiPlane488GenSourceBlock5
import QiushiPlane488GenSourceBlock6
import QiushiPlane488GenSourceBlock7
import QiushiPlane488GenSourceBlock8
import QiushiPlane488GenSourceBlock9
import QiushiPlane488GenSourceBlock10
import QiushiPlane488GenSourceBlock11
import QiushiPlane488GenSourceBlock12
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenSourceAll : forall i, plane488GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 13) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488GenSourceBlock0
  | ⟨1, _⟩ => exact plane488GenSourceBlock1
  | ⟨2, _⟩ => exact plane488GenSourceBlock2
  | ⟨3, _⟩ => exact plane488GenSourceBlock3
  | ⟨4, _⟩ => exact plane488GenSourceBlock4
  | ⟨5, _⟩ => exact plane488GenSourceBlock5
  | ⟨6, _⟩ => exact plane488GenSourceBlock6
  | ⟨7, _⟩ => exact plane488GenSourceBlock7
  | ⟨8, _⟩ => exact plane488GenSourceBlock8
  | ⟨9, _⟩ => exact plane488GenSourceBlock9
  | ⟨10, _⟩ => exact plane488GenSourceBlock10
  | ⟨11, _⟩ => exact plane488GenSourceBlock11
  | ⟨12, _⟩ => exact plane488GenSourceBlock12
  | ⟨k + 13, h⟩ => omega
end QiushiMatmul
