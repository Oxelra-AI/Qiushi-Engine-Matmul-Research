import QiushiFiniteBlocks
import QiushiFrozenRank362Data
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane362RankCoverGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 24, (plane362RankCoverGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane362RankCoverGenConfig.planeBasis (i.val ^^^ (plane362RankCoverGenConfig.sectionCode j).val) = true
abbrev plane362RankCoverGenDeadProperty (i : Fin 512) : Prop :=
  (plane362RankCoverGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane362RankCoverGenConfig.deadBasis (plane362RankCoverGenConfig.deadCover i)) i.val = true
abbrev plane362RankCoverGenSourceProperty (i : Fin 31) : Prop :=
  forall g : Nat, g ∈ plane362RankCoverGenConfig.planeBasis -> spanContainsCode (plane362RankCoverGenConfig.sourceBasis i) g = true
abbrev plane362RankCoverGenDeadSourceProperty (i : Fin 7) : Prop :=
  forall g : Nat, g ∈ plane362RankCoverGenConfig.planeBasis -> spanContainsCode (plane362RankCoverGenConfig.deadBasis i) g = true
abbrev plane362RankCoverGenIndicatorProperty (i : Fin 31) : Prop :=
  forall j : Fin 24, plane362RankCoverGenConfig.occSys.occCoeff i j = if spanContainsCode (plane362RankCoverGenConfig.sourceBasis i) (plane362RankCoverGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane362RankCoverGenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadAll : forall i, plane362RankCoverGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane362RankCoverGenDeadBlock0
  | ⟨1, _⟩ => exact plane362RankCoverGenDeadBlock1
  | ⟨2, _⟩ => exact plane362RankCoverGenDeadBlock2
  | ⟨3, _⟩ => exact plane362RankCoverGenDeadBlock3
  | ⟨4, _⟩ => exact plane362RankCoverGenDeadBlock4
  | ⟨5, _⟩ => exact plane362RankCoverGenDeadBlock5
  | ⟨6, _⟩ => exact plane362RankCoverGenDeadBlock6
  | ⟨7, _⟩ => exact plane362RankCoverGenDeadBlock7
  | ⟨8, _⟩ => exact plane362RankCoverGenDeadBlock8
  | ⟨9, _⟩ => exact plane362RankCoverGenDeadBlock9
  | ⟨10, _⟩ => exact plane362RankCoverGenDeadBlock10
  | ⟨11, _⟩ => exact plane362RankCoverGenDeadBlock11
  | ⟨12, _⟩ => exact plane362RankCoverGenDeadBlock12
  | ⟨13, _⟩ => exact plane362RankCoverGenDeadBlock13
  | ⟨14, _⟩ => exact plane362RankCoverGenDeadBlock14
  | ⟨15, _⟩ => exact plane362RankCoverGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 7,
    plane362RankCoverGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenDeadSourceProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenDeadSourceAll : forall i, plane362RankCoverGenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane362RankCoverGenDeadSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 31,
    plane362RankCoverGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenIndicatorProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenIndicatorAll : forall i, plane362RankCoverGenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane362RankCoverGenIndicatorBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane362RankCoverGenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSectionProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSectionAll : forall i, plane362RankCoverGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane362RankCoverGenSectionBlock0
  | ⟨1, _⟩ => exact plane362RankCoverGenSectionBlock1
  | ⟨2, _⟩ => exact plane362RankCoverGenSectionBlock2
  | ⟨3, _⟩ => exact plane362RankCoverGenSectionBlock3
  | ⟨4, _⟩ => exact plane362RankCoverGenSectionBlock4
  | ⟨5, _⟩ => exact plane362RankCoverGenSectionBlock5
  | ⟨6, _⟩ => exact plane362RankCoverGenSectionBlock6
  | ⟨7, _⟩ => exact plane362RankCoverGenSectionBlock7
  | ⟨8, _⟩ => exact plane362RankCoverGenSectionBlock8
  | ⟨9, _⟩ => exact plane362RankCoverGenSectionBlock9
  | ⟨10, _⟩ => exact plane362RankCoverGenSectionBlock10
  | ⟨11, _⟩ => exact plane362RankCoverGenSectionBlock11
  | ⟨12, _⟩ => exact plane362RankCoverGenSectionBlock12
  | ⟨13, _⟩ => exact plane362RankCoverGenSectionBlock13
  | ⟨14, _⟩ => exact plane362RankCoverGenSectionBlock14
  | ⟨15, _⟩ => exact plane362RankCoverGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 31,
    plane362RankCoverGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane362RankCoverGenSourceProperty, plane362RankCoverGenConfig, plane362RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenSourceAll : forall i, plane362RankCoverGenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane362RankCoverGenSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul
