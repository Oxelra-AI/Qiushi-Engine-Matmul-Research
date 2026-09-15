import QiushiPlane485GenData
import QiushiFrozenWangSpaces003
import QiushiFrozenWangSpaces004
import QiushiFrozenWangSpaces005
import QiushiFrozenWangSpaces056

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane485_source0128 : plane485GenConfig.sourceLb (128 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (128 : Fin 421)) := by
  change plane485GenSourceLb (128 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (128 : Fin 421)))
  rw [show plane485GenSourceLb (128 : Fin 421) = 16 by decide,
      show plane485GenSourceBasis (128 : Fin 421) = [420, 66, 20, 10] by decide]
  exact space1793_lower

theorem plane485_source0129 : plane485GenConfig.sourceLb (129 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (129 : Fin 421)) := by
  change plane485GenSourceLb (129 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (129 : Fin 421)))
  rw [show plane485GenSourceLb (129 : Fin 421) = 16 by decide,
      show plane485GenSourceBasis (129 : Fin 421) = [323, 130, 39, 20, 10] by decide]
  exact space1794_lower

theorem plane485_source0130 : plane485GenConfig.sourceLb (130 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (130 : Fin 421)) := by
  change plane485GenSourceLb (130 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (130 : Fin 421)))
  rw [show plane485GenSourceLb (130 : Fin 421) = 16 by decide,
      show plane485GenSourceBasis (130 : Fin 421) = [262, 192, 32, 20, 10] by decide]
  exact space1795_lower

theorem plane485_source0131 : plane485GenConfig.sourceLb (131 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (131 : Fin 421)) := by
  change plane485GenSourceLb (131 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (131 : Fin 421)))
  rw [show plane485GenSourceLb (131 : Fin 421) = 16 by decide,
      show plane485GenSourceBasis (131 : Fin 421) = [258, 197, 32, 20, 10] by decide]
  exact space1796_lower

theorem plane485_source0132 : plane485GenConfig.sourceLb (132 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (132 : Fin 421)) := by
  change plane485GenSourceLb (132 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (132 : Fin 421)))
  rw [show plane485GenSourceLb (132 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (132 : Fin 421) = [32, 20, 8, 2, 1] by decide]
  exact space1797_lower

theorem plane485_source0133 : plane485GenConfig.sourceLb (133 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (133 : Fin 421)) := by
  change plane485GenSourceLb (133 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (133 : Fin 421)))
  rw [show plane485GenSourceLb (133 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (133 : Fin 421) = [32, 16, 10, 4, 1] by decide]
  exact space1798_lower

theorem plane485_source0134 : plane485GenConfig.sourceLb (134 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (134 : Fin 421)) := by
  change plane485GenSourceLb (134 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (134 : Fin 421)))
  rw [show plane485GenSourceLb (134 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (134 : Fin 421) = [34, 18, 10, 6, 1] by decide]
  exact space0120_lower

theorem plane485_source0135 : plane485GenConfig.sourceLb (135 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (135 : Fin 421)) := by
  change plane485GenSourceLb (135 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (135 : Fin 421)))
  rw [show plane485GenSourceLb (135 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (135 : Fin 421) = [33, 17, 8, 5, 2] by decide]
  exact space0122_lower

theorem plane485_source0136 : plane485GenConfig.sourceLb (136 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (136 : Fin 421)) := by
  change plane485GenSourceLb (136 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (136 : Fin 421)))
  rw [show plane485GenSourceLb (136 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (136 : Fin 421) = [33, 16, 9, 4, 3] by decide]
  exact space0123_lower

theorem plane485_source0137 : plane485GenConfig.sourceLb (137 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (137 : Fin 421)) := by
  change plane485GenSourceLb (137 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (137 : Fin 421)))
  rw [show plane485GenSourceLb (137 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (137 : Fin 421) = [32, 17, 9, 5, 3] by decide]
  exact space1799_lower

theorem plane485_source0138 : plane485GenConfig.sourceLb (138 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (138 : Fin 421)) := by
  change plane485GenSourceLb (138 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (138 : Fin 421)))
  rw [show plane485GenSourceLb (138 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (138 : Fin 421) = [32, 16, 9, 4, 3] by decide]
  exact space0126_lower

theorem plane485_source0139 : plane485GenConfig.sourceLb (139 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (139 : Fin 421)) := by
  change plane485GenSourceLb (139 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (139 : Fin 421)))
  rw [show plane485GenSourceLb (139 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (139 : Fin 421) = [32, 17, 8, 5, 2] by decide]
  exact space0127_lower

theorem plane485_source0140 : plane485GenConfig.sourceLb (140 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (140 : Fin 421)) := by
  change plane485GenSourceLb (140 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (140 : Fin 421)))
  rw [show plane485GenSourceLb (140 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (140 : Fin 421) = [33, 16, 8, 4, 2] by decide]
  exact space1800_lower

theorem plane485_source0141 : plane485GenConfig.sourceLb (141 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (141 : Fin 421)) := by
  change plane485GenSourceLb (141 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (141 : Fin 421)))
  rw [show plane485GenSourceLb (141 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (141 : Fin 421) = [32, 18, 10, 6, 1] by decide]
  exact space0129_lower

theorem plane485_source0142 : plane485GenConfig.sourceLb (142 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (142 : Fin 421)) := by
  change plane485GenSourceLb (142 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (142 : Fin 421)))
  rw [show plane485GenSourceLb (142 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (142 : Fin 421) = [34, 16, 10, 4, 1] by decide]
  exact space1801_lower

theorem plane485_source0143 : plane485GenConfig.sourceLb (143 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (143 : Fin 421)) := by
  change plane485GenSourceLb (143 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (143 : Fin 421)))
  rw [show plane485GenSourceLb (143 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (143 : Fin 421) = [36, 20, 8, 2, 1] by decide]
  exact space1802_lower

theorem plane485_source0144 : plane485GenConfig.sourceLb (144 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (144 : Fin 421)) := by
  change plane485GenSourceLb (144 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (144 : Fin 421)))
  rw [show plane485GenSourceLb (144 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (144 : Fin 421) = [68, 32, 20, 8, 2, 1] by decide]
  exact space1803_lower

theorem plane485_source0145 : plane485GenConfig.sourceLb (145 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (145 : Fin 421)) := by
  change plane485GenSourceLb (145 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (145 : Fin 421)))
  rw [show plane485GenSourceLb (145 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (145 : Fin 421) = [129, 33, 16, 8, 4, 2] by decide]
  exact space1804_lower

theorem plane485_source0146 : plane485GenConfig.sourceLb (146 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (146 : Fin 421)) := by
  change plane485GenSourceLb (146 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (146 : Fin 421)))
  rw [show plane485GenSourceLb (146 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (146 : Fin 421) = [128, 64, 20, 8, 2] by decide]
  exact space1805_lower

theorem plane485_source0147 : plane485GenConfig.sourceLb (147 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (147 : Fin 421)) := by
  change plane485GenSourceLb (147 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (147 : Fin 421)))
  rw [show plane485GenSourceLb (147 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (147 : Fin 421) = [129, 65, 20, 9, 3] by decide]
  exact space1806_lower

theorem plane485_source0148 : plane485GenConfig.sourceLb (148 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (148 : Fin 421)) := by
  change plane485GenSourceLb (148 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (148 : Fin 421)))
  rw [show plane485GenSourceLb (148 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (148 : Fin 421) = [128, 64, 20, 9, 3] by decide]
  exact space1807_lower

theorem plane485_source0149 : plane485GenConfig.sourceLb (149 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (149 : Fin 421)) := by
  change plane485GenSourceLb (149 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (149 : Fin 421)))
  rw [show plane485GenSourceLb (149 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (149 : Fin 421) = [128, 65, 20, 8, 2] by decide]
  exact space1808_lower

theorem plane485_source0150 : plane485GenConfig.sourceLb (150 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (150 : Fin 421)) := by
  change plane485GenSourceLb (150 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (150 : Fin 421)))
  rw [show plane485GenSourceLb (150 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (150 : Fin 421) = [132, 68, 20, 8, 2, 1] by decide]
  exact space1809_lower

theorem plane485_source0151 : plane485GenConfig.sourceLb (151 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (151 : Fin 421)) := by
  change plane485GenSourceLb (151 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (151 : Fin 421)))
  rw [show plane485GenSourceLb (151 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (151 : Fin 421) = [132, 64, 20, 8, 2] by decide]
  exact space1810_lower

theorem plane485_source0152 : plane485GenConfig.sourceLb (152 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (152 : Fin 421)) := by
  change plane485GenSourceLb (152 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (152 : Fin 421)))
  rw [show plane485GenSourceLb (152 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (152 : Fin 421) = [133, 64, 20, 9, 3] by decide]
  exact space1811_lower

theorem plane485_source0153 : plane485GenConfig.sourceLb (153 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (153 : Fin 421)) := by
  change plane485GenSourceLb (153 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (153 : Fin 421)))
  rw [show plane485GenSourceLb (153 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (153 : Fin 421) = [132, 65, 20, 9, 3] by decide]
  exact space1812_lower

theorem plane485_source0154 : plane485GenConfig.sourceLb (154 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (154 : Fin 421)) := by
  change plane485GenSourceLb (154 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (154 : Fin 421)))
  rw [show plane485GenSourceLb (154 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (154 : Fin 421) = [132, 65, 20, 8, 2] by decide]
  exact space1813_lower

theorem plane485_source0155 : plane485GenConfig.sourceLb (155 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (155 : Fin 421)) := by
  change plane485GenSourceLb (155 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (155 : Fin 421)))
  rw [show plane485GenSourceLb (155 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (155 : Fin 421) = [128, 68, 20, 8, 2, 1] by decide]
  exact space1814_lower

theorem plane485_source0156 : plane485GenConfig.sourceLb (156 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (156 : Fin 421)) := by
  change plane485GenSourceLb (156 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (156 : Fin 421)))
  rw [show plane485GenSourceLb (156 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (156 : Fin 421) = [193, 32, 17, 9, 5, 3] by decide]
  exact space1815_lower

theorem plane485_source0157 : plane485GenConfig.sourceLb (157 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (157 : Fin 421)) := by
  change plane485GenSourceLb (157 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (157 : Fin 421)))
  rw [show plane485GenSourceLb (157 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (157 : Fin 421) = [260, 64, 38, 20, 10] by decide]
  exact space1816_lower

theorem plane485_source0158 : plane485GenConfig.sourceLb (158 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (158 : Fin 421)) := by
  change plane485GenSourceLb (158 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (158 : Fin 421)))
  rw [show plane485GenSourceLb (158 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (158 : Fin 421) = [291, 65, 19, 10, 7] by decide]
  exact space0174_lower

theorem plane485_source0159 : plane485GenConfig.sourceLb (159 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (159 : Fin 421)) := by
  change plane485GenSourceLb (159 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (159 : Fin 421)))
  rw [show plane485GenSourceLb (159 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (159 : Fin 421) = [258, 66, 38, 20, 10] by decide]
  exact space1817_lower

theorem plane485_sourceBlock004 (offset : Fin 32)
    (hlt : 4 * 32 + offset.val < 421) :
    plane485GenConfig.sourceLb (Fin.mk (4 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (Fin.mk (4 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane485_source0128
  | ⟨1, _⟩ => intro hlt; exact plane485_source0129
  | ⟨2, _⟩ => intro hlt; exact plane485_source0130
  | ⟨3, _⟩ => intro hlt; exact plane485_source0131
  | ⟨4, _⟩ => intro hlt; exact plane485_source0132
  | ⟨5, _⟩ => intro hlt; exact plane485_source0133
  | ⟨6, _⟩ => intro hlt; exact plane485_source0134
  | ⟨7, _⟩ => intro hlt; exact plane485_source0135
  | ⟨8, _⟩ => intro hlt; exact plane485_source0136
  | ⟨9, _⟩ => intro hlt; exact plane485_source0137
  | ⟨10, _⟩ => intro hlt; exact plane485_source0138
  | ⟨11, _⟩ => intro hlt; exact plane485_source0139
  | ⟨12, _⟩ => intro hlt; exact plane485_source0140
  | ⟨13, _⟩ => intro hlt; exact plane485_source0141
  | ⟨14, _⟩ => intro hlt; exact plane485_source0142
  | ⟨15, _⟩ => intro hlt; exact plane485_source0143
  | ⟨16, _⟩ => intro hlt; exact plane485_source0144
  | ⟨17, _⟩ => intro hlt; exact plane485_source0145
  | ⟨18, _⟩ => intro hlt; exact plane485_source0146
  | ⟨19, _⟩ => intro hlt; exact plane485_source0147
  | ⟨20, _⟩ => intro hlt; exact plane485_source0148
  | ⟨21, _⟩ => intro hlt; exact plane485_source0149
  | ⟨22, _⟩ => intro hlt; exact plane485_source0150
  | ⟨23, _⟩ => intro hlt; exact plane485_source0151
  | ⟨24, _⟩ => intro hlt; exact plane485_source0152
  | ⟨25, _⟩ => intro hlt; exact plane485_source0153
  | ⟨26, _⟩ => intro hlt; exact plane485_source0154
  | ⟨27, _⟩ => intro hlt; exact plane485_source0155
  | ⟨28, _⟩ => intro hlt; exact plane485_source0156
  | ⟨29, _⟩ => intro hlt; exact plane485_source0157
  | ⟨30, _⟩ => intro hlt; exact plane485_source0158
  | ⟨31, _⟩ => intro hlt; exact plane485_source0159
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
