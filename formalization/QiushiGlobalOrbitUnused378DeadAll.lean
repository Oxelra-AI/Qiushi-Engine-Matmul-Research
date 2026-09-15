import QiushiGlobalOrbitUnused378DeadBlock0
import QiushiGlobalOrbitUnused378DeadBlock1
import QiushiGlobalOrbitUnused378DeadBlock2
import QiushiGlobalOrbitUnused378DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane378UnusedGenDeadAll : forall i, plane378UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane378UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane378UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane378UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane378UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
