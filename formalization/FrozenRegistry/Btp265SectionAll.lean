import FrozenRegistry.Btp265SectionBlock0
import FrozenRegistry.Btp265SectionBlock1
import FrozenRegistry.Btp265SectionBlock2
import FrozenRegistry.Btp265SectionBlock3
import FrozenRegistry.Btp265SectionBlock4
import FrozenRegistry.Btp265SectionBlock5
import FrozenRegistry.Btp265SectionBlock6
import FrozenRegistry.Btp265SectionBlock7
import FrozenRegistry.Btp265SectionBlock8
import FrozenRegistry.Btp265SectionBlock9
import FrozenRegistry.Btp265SectionBlock10
import FrozenRegistry.Btp265SectionBlock11
import FrozenRegistry.Btp265SectionBlock12
import FrozenRegistry.Btp265SectionBlock13
import FrozenRegistry.Btp265SectionBlock14
import FrozenRegistry.Btp265SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane265BtpGenSectionAll : forall i, plane265BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane265BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane265BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane265BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane265BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane265BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane265BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane265BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane265BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane265BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane265BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane265BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane265BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane265BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane265BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane265BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane265BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
