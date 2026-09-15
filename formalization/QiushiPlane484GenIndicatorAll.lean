import QiushiPlane484GenIndicatorBlock0
import QiushiPlane484GenIndicatorBlock1
import QiushiPlane484GenIndicatorBlock2
import QiushiPlane484GenIndicatorBlock3
import QiushiPlane484GenIndicatorBlock4
import QiushiPlane484GenIndicatorBlock5
import QiushiPlane484GenIndicatorBlock6
import QiushiPlane484GenIndicatorBlock7
import QiushiPlane484GenIndicatorBlock8
import QiushiPlane484GenIndicatorBlock9
import QiushiPlane484GenIndicatorBlock10
import QiushiPlane484GenIndicatorBlock11
import QiushiPlane484GenIndicatorBlock12
import QiushiPlane484GenIndicatorBlock13
import QiushiPlane484GenIndicatorBlock14
import QiushiPlane484GenIndicatorBlock15
import QiushiPlane484GenIndicatorBlock16
import QiushiPlane484GenIndicatorBlock17
import QiushiPlane484GenIndicatorBlock18
import QiushiPlane484GenIndicatorBlock19
import QiushiPlane484GenIndicatorBlock20
import QiushiPlane484GenIndicatorBlock21
import QiushiPlane484GenIndicatorBlock22
import QiushiPlane484GenIndicatorBlock23
import QiushiPlane484GenIndicatorBlock24
import QiushiPlane484GenIndicatorBlock25
import QiushiPlane484GenIndicatorBlock26
import QiushiPlane484GenIndicatorBlock27
import QiushiPlane484GenIndicatorBlock28
import QiushiPlane484GenIndicatorBlock29
import QiushiPlane484GenIndicatorBlock30
import QiushiPlane484GenIndicatorBlock31
import QiushiPlane484GenIndicatorBlock32
import QiushiPlane484GenIndicatorBlock33
import QiushiPlane484GenIndicatorBlock34
import QiushiPlane484GenIndicatorBlock35
import QiushiPlane484GenIndicatorBlock36
import QiushiPlane484GenIndicatorBlock37
import QiushiPlane484GenIndicatorBlock38
import QiushiPlane484GenIndicatorBlock39
import QiushiPlane484GenIndicatorBlock40
import QiushiPlane484GenIndicatorBlock41
import QiushiPlane484GenIndicatorBlock42
import QiushiPlane484GenIndicatorBlock43
import QiushiPlane484GenIndicatorBlock44
import QiushiPlane484GenIndicatorBlock45
import QiushiPlane484GenIndicatorBlock46
import QiushiPlane484GenIndicatorBlock47
import QiushiPlane484GenIndicatorBlock48
import QiushiPlane484GenIndicatorBlock49
import QiushiPlane484GenIndicatorBlock50
import QiushiPlane484GenIndicatorBlock51
import QiushiPlane484GenIndicatorBlock52
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane484GenIndicatorAll : forall i, plane484GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 53) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane484GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane484GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane484GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane484GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane484GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane484GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane484GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane484GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane484GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane484GenIndicatorBlock9
  | ⟨10, _⟩ => exact plane484GenIndicatorBlock10
  | ⟨11, _⟩ => exact plane484GenIndicatorBlock11
  | ⟨12, _⟩ => exact plane484GenIndicatorBlock12
  | ⟨13, _⟩ => exact plane484GenIndicatorBlock13
  | ⟨14, _⟩ => exact plane484GenIndicatorBlock14
  | ⟨15, _⟩ => exact plane484GenIndicatorBlock15
  | ⟨16, _⟩ => exact plane484GenIndicatorBlock16
  | ⟨17, _⟩ => exact plane484GenIndicatorBlock17
  | ⟨18, _⟩ => exact plane484GenIndicatorBlock18
  | ⟨19, _⟩ => exact plane484GenIndicatorBlock19
  | ⟨20, _⟩ => exact plane484GenIndicatorBlock20
  | ⟨21, _⟩ => exact plane484GenIndicatorBlock21
  | ⟨22, _⟩ => exact plane484GenIndicatorBlock22
  | ⟨23, _⟩ => exact plane484GenIndicatorBlock23
  | ⟨24, _⟩ => exact plane484GenIndicatorBlock24
  | ⟨25, _⟩ => exact plane484GenIndicatorBlock25
  | ⟨26, _⟩ => exact plane484GenIndicatorBlock26
  | ⟨27, _⟩ => exact plane484GenIndicatorBlock27
  | ⟨28, _⟩ => exact plane484GenIndicatorBlock28
  | ⟨29, _⟩ => exact plane484GenIndicatorBlock29
  | ⟨30, _⟩ => exact plane484GenIndicatorBlock30
  | ⟨31, _⟩ => exact plane484GenIndicatorBlock31
  | ⟨32, _⟩ => exact plane484GenIndicatorBlock32
  | ⟨33, _⟩ => exact plane484GenIndicatorBlock33
  | ⟨34, _⟩ => exact plane484GenIndicatorBlock34
  | ⟨35, _⟩ => exact plane484GenIndicatorBlock35
  | ⟨36, _⟩ => exact plane484GenIndicatorBlock36
  | ⟨37, _⟩ => exact plane484GenIndicatorBlock37
  | ⟨38, _⟩ => exact plane484GenIndicatorBlock38
  | ⟨39, _⟩ => exact plane484GenIndicatorBlock39
  | ⟨40, _⟩ => exact plane484GenIndicatorBlock40
  | ⟨41, _⟩ => exact plane484GenIndicatorBlock41
  | ⟨42, _⟩ => exact plane484GenIndicatorBlock42
  | ⟨43, _⟩ => exact plane484GenIndicatorBlock43
  | ⟨44, _⟩ => exact plane484GenIndicatorBlock44
  | ⟨45, _⟩ => exact plane484GenIndicatorBlock45
  | ⟨46, _⟩ => exact plane484GenIndicatorBlock46
  | ⟨47, _⟩ => exact plane484GenIndicatorBlock47
  | ⟨48, _⟩ => exact plane484GenIndicatorBlock48
  | ⟨49, _⟩ => exact plane484GenIndicatorBlock49
  | ⟨50, _⟩ => exact plane484GenIndicatorBlock50
  | ⟨51, _⟩ => exact plane484GenIndicatorBlock51
  | ⟨52, _⟩ => exact plane484GenIndicatorBlock52
  | ⟨k + 53, h⟩ => omega
end QiushiMatmul
