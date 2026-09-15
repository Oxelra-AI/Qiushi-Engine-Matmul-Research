import QiushiFiniteBlocks
import QiushiFrozenRank363Data
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane363RankCoverGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 19, (plane363RankCoverGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane363RankCoverGenConfig.planeBasis (i.val ^^^ (plane363RankCoverGenConfig.sectionCode j).val) = true
abbrev plane363RankCoverGenDeadProperty (i : Fin 512) : Prop :=
  (plane363RankCoverGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane363RankCoverGenConfig.deadBasis (plane363RankCoverGenConfig.deadCover i)) i.val = true
abbrev plane363RankCoverGenSourceProperty (i : Fin 33) : Prop :=
  forall g : Nat, g ∈ plane363RankCoverGenConfig.planeBasis -> spanContainsCode (plane363RankCoverGenConfig.sourceBasis i) g = true
abbrev plane363RankCoverGenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane363RankCoverGenConfig.planeBasis -> spanContainsCode (plane363RankCoverGenConfig.deadBasis i) g = true
abbrev plane363RankCoverGenIndicatorProperty (i : Fin 33) : Prop :=
  forall j : Fin 19, plane363RankCoverGenConfig.occSys.occCoeff i j = if spanContainsCode (plane363RankCoverGenConfig.sourceBasis i) (plane363RankCoverGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane363RankCoverGenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadAll : forall i, plane363RankCoverGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane363RankCoverGenDeadBlock0
  | ⟨1, _⟩ => exact plane363RankCoverGenDeadBlock1
  | ⟨2, _⟩ => exact plane363RankCoverGenDeadBlock2
  | ⟨3, _⟩ => exact plane363RankCoverGenDeadBlock3
  | ⟨4, _⟩ => exact plane363RankCoverGenDeadBlock4
  | ⟨5, _⟩ => exact plane363RankCoverGenDeadBlock5
  | ⟨6, _⟩ => exact plane363RankCoverGenDeadBlock6
  | ⟨7, _⟩ => exact plane363RankCoverGenDeadBlock7
  | ⟨8, _⟩ => exact plane363RankCoverGenDeadBlock8
  | ⟨9, _⟩ => exact plane363RankCoverGenDeadBlock9
  | ⟨10, _⟩ => exact plane363RankCoverGenDeadBlock10
  | ⟨11, _⟩ => exact plane363RankCoverGenDeadBlock11
  | ⟨12, _⟩ => exact plane363RankCoverGenDeadBlock12
  | ⟨13, _⟩ => exact plane363RankCoverGenDeadBlock13
  | ⟨14, _⟩ => exact plane363RankCoverGenDeadBlock14
  | ⟨15, _⟩ => exact plane363RankCoverGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 13,
    plane363RankCoverGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenDeadSourceProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenDeadSourceAll : forall i, plane363RankCoverGenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane363RankCoverGenDeadSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 33,
    plane363RankCoverGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenIndicatorProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 33,
    plane363RankCoverGenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenIndicatorProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenIndicatorAll : forall i, plane363RankCoverGenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 2) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane363RankCoverGenIndicatorBlock0
  | ⟨1, _⟩ => exact plane363RankCoverGenIndicatorBlock1
  | ⟨k + 2, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane363RankCoverGenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSectionProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSectionAll : forall i, plane363RankCoverGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane363RankCoverGenSectionBlock0
  | ⟨1, _⟩ => exact plane363RankCoverGenSectionBlock1
  | ⟨2, _⟩ => exact plane363RankCoverGenSectionBlock2
  | ⟨3, _⟩ => exact plane363RankCoverGenSectionBlock3
  | ⟨4, _⟩ => exact plane363RankCoverGenSectionBlock4
  | ⟨5, _⟩ => exact plane363RankCoverGenSectionBlock5
  | ⟨6, _⟩ => exact plane363RankCoverGenSectionBlock6
  | ⟨7, _⟩ => exact plane363RankCoverGenSectionBlock7
  | ⟨8, _⟩ => exact plane363RankCoverGenSectionBlock8
  | ⟨9, _⟩ => exact plane363RankCoverGenSectionBlock9
  | ⟨10, _⟩ => exact plane363RankCoverGenSectionBlock10
  | ⟨11, _⟩ => exact plane363RankCoverGenSectionBlock11
  | ⟨12, _⟩ => exact plane363RankCoverGenSectionBlock12
  | ⟨13, _⟩ => exact plane363RankCoverGenSectionBlock13
  | ⟨14, _⟩ => exact plane363RankCoverGenSectionBlock14
  | ⟨15, _⟩ => exact plane363RankCoverGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 33,
    plane363RankCoverGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSourceProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 33,
    plane363RankCoverGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane363RankCoverGenSourceProperty, plane363RankCoverGenConfig, plane363RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenSourceAll : forall i, plane363RankCoverGenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 2) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane363RankCoverGenSourceBlock0
  | ⟨1, _⟩ => exact plane363RankCoverGenSourceBlock1
  | ⟨k + 2, h⟩ => omega
end QiushiMatmul
