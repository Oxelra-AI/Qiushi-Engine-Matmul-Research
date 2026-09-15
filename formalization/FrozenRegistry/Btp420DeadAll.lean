import FrozenRegistry.Btp420DeadBlock0
import FrozenRegistry.Btp420DeadBlock1
import FrozenRegistry.Btp420DeadBlock2
import FrozenRegistry.Btp420DeadBlock3
import FrozenRegistry.Btp420DeadBlock4
import FrozenRegistry.Btp420DeadBlock5
import FrozenRegistry.Btp420DeadBlock6
import FrozenRegistry.Btp420DeadBlock7
import FrozenRegistry.Btp420DeadBlock8
import FrozenRegistry.Btp420DeadBlock9
import FrozenRegistry.Btp420DeadBlock10
import FrozenRegistry.Btp420DeadBlock11
import FrozenRegistry.Btp420DeadBlock12
import FrozenRegistry.Btp420DeadBlock13
import FrozenRegistry.Btp420DeadBlock14
import FrozenRegistry.Btp420DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane420BtpGenDeadAll : forall i, plane420BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane420BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane420BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane420BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane420BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane420BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane420BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane420BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane420BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane420BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane420BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane420BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane420BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane420BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane420BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane420BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane420BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
