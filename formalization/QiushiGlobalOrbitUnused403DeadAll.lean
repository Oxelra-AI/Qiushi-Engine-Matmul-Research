import QiushiGlobalOrbitUnused403DeadBlock0
import QiushiGlobalOrbitUnused403DeadBlock1
import QiushiGlobalOrbitUnused403DeadBlock2
import QiushiGlobalOrbitUnused403DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane403UnusedGenDeadAll : forall i, plane403UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane403UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane403UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane403UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane403UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
