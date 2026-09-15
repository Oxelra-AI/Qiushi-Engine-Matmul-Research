import FrozenRegistry.Btp410DeadBlock0
import FrozenRegistry.Btp410DeadBlock1
import FrozenRegistry.Btp410DeadBlock2
import FrozenRegistry.Btp410DeadBlock3
import FrozenRegistry.Btp410DeadBlock4
import FrozenRegistry.Btp410DeadBlock5
import FrozenRegistry.Btp410DeadBlock6
import FrozenRegistry.Btp410DeadBlock7
import FrozenRegistry.Btp410DeadBlock8
import FrozenRegistry.Btp410DeadBlock9
import FrozenRegistry.Btp410DeadBlock10
import FrozenRegistry.Btp410DeadBlock11
import FrozenRegistry.Btp410DeadBlock12
import FrozenRegistry.Btp410DeadBlock13
import FrozenRegistry.Btp410DeadBlock14
import FrozenRegistry.Btp410DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane410BtpGenDeadAll : forall i, plane410BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane410BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane410BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane410BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane410BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane410BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane410BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane410BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane410BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane410BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane410BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane410BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane410BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane410BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane410BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane410BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane410BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
