import QiushiGlobalOrbitUnused356DeadBlock0
import QiushiGlobalOrbitUnused356DeadBlock1
import QiushiGlobalOrbitUnused356DeadBlock2
import QiushiGlobalOrbitUnused356DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane356UnusedGenDeadAll : forall i, plane356UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane356UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane356UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane356UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane356UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
