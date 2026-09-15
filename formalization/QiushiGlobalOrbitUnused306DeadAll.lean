import QiushiGlobalOrbitUnused306DeadBlock0
import QiushiGlobalOrbitUnused306DeadBlock1
import QiushiGlobalOrbitUnused306DeadBlock2
import QiushiGlobalOrbitUnused306DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane306UnusedGenDeadAll : forall i, plane306UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane306UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane306UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane306UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane306UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
