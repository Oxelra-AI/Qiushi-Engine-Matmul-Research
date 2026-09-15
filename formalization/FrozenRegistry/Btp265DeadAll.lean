import FrozenRegistry.Btp265DeadBlock0
import FrozenRegistry.Btp265DeadBlock1
import FrozenRegistry.Btp265DeadBlock2
import FrozenRegistry.Btp265DeadBlock3
import FrozenRegistry.Btp265DeadBlock4
import FrozenRegistry.Btp265DeadBlock5
import FrozenRegistry.Btp265DeadBlock6
import FrozenRegistry.Btp265DeadBlock7
import FrozenRegistry.Btp265DeadBlock8
import FrozenRegistry.Btp265DeadBlock9
import FrozenRegistry.Btp265DeadBlock10
import FrozenRegistry.Btp265DeadBlock11
import FrozenRegistry.Btp265DeadBlock12
import FrozenRegistry.Btp265DeadBlock13
import FrozenRegistry.Btp265DeadBlock14
import FrozenRegistry.Btp265DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane265BtpGenDeadAll : forall i, plane265BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane265BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane265BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane265BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane265BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane265BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane265BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane265BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane265BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane265BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane265BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane265BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane265BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane265BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane265BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane265BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane265BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
