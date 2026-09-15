import QiushiPlane484GenSourceBlock0
import QiushiPlane484GenSourceBlock1
import QiushiPlane484GenSourceBlock2
import QiushiPlane484GenSourceBlock3
import QiushiPlane484GenSourceBlock4
import QiushiPlane484GenSourceBlock5
import QiushiPlane484GenSourceBlock6
import QiushiPlane484GenSourceBlock7
import QiushiPlane484GenSourceBlock8
import QiushiPlane484GenSourceBlock9
import QiushiPlane484GenSourceBlock10
import QiushiPlane484GenSourceBlock11
import QiushiPlane484GenSourceBlock12
import QiushiPlane484GenSourceBlock13
import QiushiPlane484GenSourceBlock14
import QiushiPlane484GenSourceBlock15
import QiushiPlane484GenSourceBlock16
import QiushiPlane484GenSourceBlock17
import QiushiPlane484GenSourceBlock18
import QiushiPlane484GenSourceBlock19
import QiushiPlane484GenSourceBlock20
import QiushiPlane484GenSourceBlock21
import QiushiPlane484GenSourceBlock22
import QiushiPlane484GenSourceBlock23
import QiushiPlane484GenSourceBlock24
import QiushiPlane484GenSourceBlock25
import QiushiPlane484GenSourceBlock26
import QiushiPlane484GenSourceBlock27
import QiushiPlane484GenSourceBlock28
import QiushiPlane484GenSourceBlock29
import QiushiPlane484GenSourceBlock30
import QiushiPlane484GenSourceBlock31
import QiushiPlane484GenSourceBlock32
import QiushiPlane484GenSourceBlock33
import QiushiPlane484GenSourceBlock34
import QiushiPlane484GenSourceBlock35
import QiushiPlane484GenSourceBlock36
import QiushiPlane484GenSourceBlock37
import QiushiPlane484GenSourceBlock38
import QiushiPlane484GenSourceBlock39
import QiushiPlane484GenSourceBlock40
import QiushiPlane484GenSourceBlock41
import QiushiPlane484GenSourceBlock42
import QiushiPlane484GenSourceBlock43
import QiushiPlane484GenSourceBlock44
import QiushiPlane484GenSourceBlock45
import QiushiPlane484GenSourceBlock46
import QiushiPlane484GenSourceBlock47
import QiushiPlane484GenSourceBlock48
import QiushiPlane484GenSourceBlock49
import QiushiPlane484GenSourceBlock50
import QiushiPlane484GenSourceBlock51
import QiushiPlane484GenSourceBlock52
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane484GenSourceAll : forall i, plane484GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 53) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane484GenSourceBlock0
  | ⟨1, _⟩ => exact plane484GenSourceBlock1
  | ⟨2, _⟩ => exact plane484GenSourceBlock2
  | ⟨3, _⟩ => exact plane484GenSourceBlock3
  | ⟨4, _⟩ => exact plane484GenSourceBlock4
  | ⟨5, _⟩ => exact plane484GenSourceBlock5
  | ⟨6, _⟩ => exact plane484GenSourceBlock6
  | ⟨7, _⟩ => exact plane484GenSourceBlock7
  | ⟨8, _⟩ => exact plane484GenSourceBlock8
  | ⟨9, _⟩ => exact plane484GenSourceBlock9
  | ⟨10, _⟩ => exact plane484GenSourceBlock10
  | ⟨11, _⟩ => exact plane484GenSourceBlock11
  | ⟨12, _⟩ => exact plane484GenSourceBlock12
  | ⟨13, _⟩ => exact plane484GenSourceBlock13
  | ⟨14, _⟩ => exact plane484GenSourceBlock14
  | ⟨15, _⟩ => exact plane484GenSourceBlock15
  | ⟨16, _⟩ => exact plane484GenSourceBlock16
  | ⟨17, _⟩ => exact plane484GenSourceBlock17
  | ⟨18, _⟩ => exact plane484GenSourceBlock18
  | ⟨19, _⟩ => exact plane484GenSourceBlock19
  | ⟨20, _⟩ => exact plane484GenSourceBlock20
  | ⟨21, _⟩ => exact plane484GenSourceBlock21
  | ⟨22, _⟩ => exact plane484GenSourceBlock22
  | ⟨23, _⟩ => exact plane484GenSourceBlock23
  | ⟨24, _⟩ => exact plane484GenSourceBlock24
  | ⟨25, _⟩ => exact plane484GenSourceBlock25
  | ⟨26, _⟩ => exact plane484GenSourceBlock26
  | ⟨27, _⟩ => exact plane484GenSourceBlock27
  | ⟨28, _⟩ => exact plane484GenSourceBlock28
  | ⟨29, _⟩ => exact plane484GenSourceBlock29
  | ⟨30, _⟩ => exact plane484GenSourceBlock30
  | ⟨31, _⟩ => exact plane484GenSourceBlock31
  | ⟨32, _⟩ => exact plane484GenSourceBlock32
  | ⟨33, _⟩ => exact plane484GenSourceBlock33
  | ⟨34, _⟩ => exact plane484GenSourceBlock34
  | ⟨35, _⟩ => exact plane484GenSourceBlock35
  | ⟨36, _⟩ => exact plane484GenSourceBlock36
  | ⟨37, _⟩ => exact plane484GenSourceBlock37
  | ⟨38, _⟩ => exact plane484GenSourceBlock38
  | ⟨39, _⟩ => exact plane484GenSourceBlock39
  | ⟨40, _⟩ => exact plane484GenSourceBlock40
  | ⟨41, _⟩ => exact plane484GenSourceBlock41
  | ⟨42, _⟩ => exact plane484GenSourceBlock42
  | ⟨43, _⟩ => exact plane484GenSourceBlock43
  | ⟨44, _⟩ => exact plane484GenSourceBlock44
  | ⟨45, _⟩ => exact plane484GenSourceBlock45
  | ⟨46, _⟩ => exact plane484GenSourceBlock46
  | ⟨47, _⟩ => exact plane484GenSourceBlock47
  | ⟨48, _⟩ => exact plane484GenSourceBlock48
  | ⟨49, _⟩ => exact plane484GenSourceBlock49
  | ⟨50, _⟩ => exact plane484GenSourceBlock50
  | ⟨51, _⟩ => exact plane484GenSourceBlock51
  | ⟨52, _⟩ => exact plane484GenSourceBlock52
  | ⟨k + 53, h⟩ => omega
end QiushiMatmul
