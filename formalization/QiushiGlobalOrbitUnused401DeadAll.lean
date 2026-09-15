import QiushiGlobalOrbitUnused401DeadBlock0
import QiushiGlobalOrbitUnused401DeadBlock1
import QiushiGlobalOrbitUnused401DeadBlock2
import QiushiGlobalOrbitUnused401DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane401UnusedGenDeadAll : forall i, plane401UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane401UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane401UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane401UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane401UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
