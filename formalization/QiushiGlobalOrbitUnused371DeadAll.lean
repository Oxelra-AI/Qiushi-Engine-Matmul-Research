import QiushiGlobalOrbitUnused371DeadBlock0
import QiushiGlobalOrbitUnused371DeadBlock1
import QiushiGlobalOrbitUnused371DeadBlock2
import QiushiGlobalOrbitUnused371DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane371UnusedGenDeadAll : forall i, plane371UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane371UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane371UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane371UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane371UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
