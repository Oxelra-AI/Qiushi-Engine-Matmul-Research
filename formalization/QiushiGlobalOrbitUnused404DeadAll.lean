import QiushiGlobalOrbitUnused404DeadBlock0
import QiushiGlobalOrbitUnused404DeadBlock1
import QiushiGlobalOrbitUnused404DeadBlock2
import QiushiGlobalOrbitUnused404DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane404UnusedGenDeadAll : forall i, plane404UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane404UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane404UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane404UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane404UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
