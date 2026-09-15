import FrozenRegistry.Btp263SectionBlock0
import FrozenRegistry.Btp263SectionBlock1
import FrozenRegistry.Btp263SectionBlock2
import FrozenRegistry.Btp263SectionBlock3
import FrozenRegistry.Btp263SectionBlock4
import FrozenRegistry.Btp263SectionBlock5
import FrozenRegistry.Btp263SectionBlock6
import FrozenRegistry.Btp263SectionBlock7
import FrozenRegistry.Btp263SectionBlock8
import FrozenRegistry.Btp263SectionBlock9
import FrozenRegistry.Btp263SectionBlock10
import FrozenRegistry.Btp263SectionBlock11
import FrozenRegistry.Btp263SectionBlock12
import FrozenRegistry.Btp263SectionBlock13
import FrozenRegistry.Btp263SectionBlock14
import FrozenRegistry.Btp263SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane263BtpGenSectionAll : forall i, plane263BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane263BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane263BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane263BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane263BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane263BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane263BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane263BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane263BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane263BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane263BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane263BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane263BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane263BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane263BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane263BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane263BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
