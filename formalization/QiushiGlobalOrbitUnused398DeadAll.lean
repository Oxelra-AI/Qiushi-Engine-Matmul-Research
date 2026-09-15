import QiushiGlobalOrbitUnused398DeadBlock0
import QiushiGlobalOrbitUnused398DeadBlock1
import QiushiGlobalOrbitUnused398DeadBlock2
import QiushiGlobalOrbitUnused398DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane398UnusedGenDeadAll : forall i, plane398UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane398UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane398UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane398UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane398UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
