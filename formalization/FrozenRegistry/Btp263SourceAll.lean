import FrozenRegistry.Btp263SourceBlock0
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane263BtpGenSourceAll : forall i, plane263BtpGenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane263BtpGenSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul
