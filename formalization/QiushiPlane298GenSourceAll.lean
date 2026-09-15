import QiushiPlane298GenSourceBlock0
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane298GenSourceAll : forall i, plane298GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane298GenSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul
