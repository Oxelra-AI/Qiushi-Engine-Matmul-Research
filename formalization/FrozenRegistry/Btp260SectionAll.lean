import FrozenRegistry.Btp260SectionBlock0
import FrozenRegistry.Btp260SectionBlock1
import FrozenRegistry.Btp260SectionBlock2
import FrozenRegistry.Btp260SectionBlock3
import FrozenRegistry.Btp260SectionBlock4
import FrozenRegistry.Btp260SectionBlock5
import FrozenRegistry.Btp260SectionBlock6
import FrozenRegistry.Btp260SectionBlock7
import FrozenRegistry.Btp260SectionBlock8
import FrozenRegistry.Btp260SectionBlock9
import FrozenRegistry.Btp260SectionBlock10
import FrozenRegistry.Btp260SectionBlock11
import FrozenRegistry.Btp260SectionBlock12
import FrozenRegistry.Btp260SectionBlock13
import FrozenRegistry.Btp260SectionBlock14
import FrozenRegistry.Btp260SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane260BtpGenSectionAll : forall i, plane260BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane260BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane260BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane260BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane260BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane260BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane260BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane260BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane260BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane260BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane260BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane260BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane260BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane260BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane260BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane260BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane260BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
