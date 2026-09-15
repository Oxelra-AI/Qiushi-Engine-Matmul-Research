import FrozenRegistry.Btp410SectionBlock0
import FrozenRegistry.Btp410SectionBlock1
import FrozenRegistry.Btp410SectionBlock2
import FrozenRegistry.Btp410SectionBlock3
import FrozenRegistry.Btp410SectionBlock4
import FrozenRegistry.Btp410SectionBlock5
import FrozenRegistry.Btp410SectionBlock6
import FrozenRegistry.Btp410SectionBlock7
import FrozenRegistry.Btp410SectionBlock8
import FrozenRegistry.Btp410SectionBlock9
import FrozenRegistry.Btp410SectionBlock10
import FrozenRegistry.Btp410SectionBlock11
import FrozenRegistry.Btp410SectionBlock12
import FrozenRegistry.Btp410SectionBlock13
import FrozenRegistry.Btp410SectionBlock14
import FrozenRegistry.Btp410SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane410BtpGenSectionAll : forall i, plane410BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane410BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane410BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane410BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane410BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane410BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane410BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane410BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane410BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane410BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane410BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane410BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane410BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane410BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane410BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane410BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane410BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
