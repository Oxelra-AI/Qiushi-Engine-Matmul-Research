import FrozenRegistry.Btp227SectionBlock0
import FrozenRegistry.Btp227SectionBlock1
import FrozenRegistry.Btp227SectionBlock2
import FrozenRegistry.Btp227SectionBlock3
import FrozenRegistry.Btp227SectionBlock4
import FrozenRegistry.Btp227SectionBlock5
import FrozenRegistry.Btp227SectionBlock6
import FrozenRegistry.Btp227SectionBlock7
import FrozenRegistry.Btp227SectionBlock8
import FrozenRegistry.Btp227SectionBlock9
import FrozenRegistry.Btp227SectionBlock10
import FrozenRegistry.Btp227SectionBlock11
import FrozenRegistry.Btp227SectionBlock12
import FrozenRegistry.Btp227SectionBlock13
import FrozenRegistry.Btp227SectionBlock14
import FrozenRegistry.Btp227SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane227BtpGenSectionAll : forall i, plane227BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane227BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane227BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane227BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane227BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane227BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane227BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane227BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane227BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane227BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane227BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane227BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane227BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane227BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane227BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane227BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane227BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
