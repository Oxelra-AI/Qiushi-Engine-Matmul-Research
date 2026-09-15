import QiushiPlane463GenSourceBlock0
import QiushiPlane463GenSourceBlock1
import QiushiPlane463GenSourceBlock2
import QiushiPlane463GenSourceBlock3
import QiushiPlane463GenSourceBlock4
import QiushiPlane463GenSourceBlock5
import QiushiPlane463GenSourceBlock6
import QiushiPlane463GenSourceBlock7
import QiushiPlane463GenSourceBlock8
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463GenSourceAll : forall i, plane463GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 9) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane463GenSourceBlock0
  | ⟨1, _⟩ => exact plane463GenSourceBlock1
  | ⟨2, _⟩ => exact plane463GenSourceBlock2
  | ⟨3, _⟩ => exact plane463GenSourceBlock3
  | ⟨4, _⟩ => exact plane463GenSourceBlock4
  | ⟨5, _⟩ => exact plane463GenSourceBlock5
  | ⟨6, _⟩ => exact plane463GenSourceBlock6
  | ⟨7, _⟩ => exact plane463GenSourceBlock7
  | ⟨8, _⟩ => exact plane463GenSourceBlock8
  | ⟨k + 9, h⟩ => omega
end QiushiMatmul
