import QiushiGlobalOrbitUnused307DeadBlock0
import QiushiGlobalOrbitUnused307DeadBlock1
import QiushiGlobalOrbitUnused307DeadBlock2
import QiushiGlobalOrbitUnused307DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane307UnusedGenDeadAll : forall i, plane307UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane307UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane307UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane307UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane307UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
