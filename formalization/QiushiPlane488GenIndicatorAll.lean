import QiushiPlane488GenIndicatorBlock0
import QiushiPlane488GenIndicatorBlock1
import QiushiPlane488GenIndicatorBlock2
import QiushiPlane488GenIndicatorBlock3
import QiushiPlane488GenIndicatorBlock4
import QiushiPlane488GenIndicatorBlock5
import QiushiPlane488GenIndicatorBlock6
import QiushiPlane488GenIndicatorBlock7
import QiushiPlane488GenIndicatorBlock8
import QiushiPlane488GenIndicatorBlock9
import QiushiPlane488GenIndicatorBlock10
import QiushiPlane488GenIndicatorBlock11
import QiushiPlane488GenIndicatorBlock12
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenIndicatorAll : forall i, plane488GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 13) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane488GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane488GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane488GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane488GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane488GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane488GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane488GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane488GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane488GenIndicatorBlock9
  | ⟨10, _⟩ => exact plane488GenIndicatorBlock10
  | ⟨11, _⟩ => exact plane488GenIndicatorBlock11
  | ⟨12, _⟩ => exact plane488GenIndicatorBlock12
  | ⟨k + 13, h⟩ => omega
end QiushiMatmul
