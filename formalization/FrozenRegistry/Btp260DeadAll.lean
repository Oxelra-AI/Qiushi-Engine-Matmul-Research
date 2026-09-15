import FrozenRegistry.Btp260DeadBlock0
import FrozenRegistry.Btp260DeadBlock1
import FrozenRegistry.Btp260DeadBlock2
import FrozenRegistry.Btp260DeadBlock3
import FrozenRegistry.Btp260DeadBlock4
import FrozenRegistry.Btp260DeadBlock5
import FrozenRegistry.Btp260DeadBlock6
import FrozenRegistry.Btp260DeadBlock7
import FrozenRegistry.Btp260DeadBlock8
import FrozenRegistry.Btp260DeadBlock9
import FrozenRegistry.Btp260DeadBlock10
import FrozenRegistry.Btp260DeadBlock11
import FrozenRegistry.Btp260DeadBlock12
import FrozenRegistry.Btp260DeadBlock13
import FrozenRegistry.Btp260DeadBlock14
import FrozenRegistry.Btp260DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane260BtpGenDeadAll : forall i, plane260BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane260BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane260BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane260BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane260BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane260BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane260BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane260BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane260BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane260BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane260BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane260BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane260BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane260BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane260BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane260BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane260BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
