import QiushiPlane484GenSources166
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane484GenBound1660 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1660 : Fin 1665))) (plane484GenSourceLb (1660 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1660 : Fin 1665) = [258, 128, 64, 34, 18, 10, 6, 1] from rfl,
      show plane484GenSourceLb (1660 : Fin 1665) = 9 from rfl]
  exact plane484GenSource1660
theorem plane484GenBound1661 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1661 : Fin 1665))) (plane484GenSourceLb (1661 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1661 : Fin 1665) = [256, 130, 66, 34, 18, 10, 4, 1] from rfl,
      show plane484GenSourceLb (1661 : Fin 1665) = 9 from rfl]
  exact plane484GenSource1661
theorem plane484GenBound1662 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1662 : Fin 1665))) (plane484GenSourceLb (1662 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1662 : Fin 1665) = [258, 130, 64, 34, 18, 10, 4, 1] from rfl,
      show plane484GenSourceLb (1662 : Fin 1665) = 9 from rfl]
  exact plane484GenSource1662
theorem plane484GenBound1663 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1663 : Fin 1665))) (plane484GenSourceLb (1663 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1663 : Fin 1665) = [258, 130, 66, 32, 18, 10, 4, 1] from rfl,
      show plane484GenSourceLb (1663 : Fin 1665) = 9 from rfl]
  exact plane484GenSource1663
theorem plane484GenBound1664 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1664 : Fin 1665))) (plane484GenSourceLb (1664 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1664 : Fin 1665) = [258, 128, 64, 32, 18, 10, 4, 1] from rfl,
      show plane484GenSourceLb (1664 : Fin 1665) = 9 from rfl]
  exact plane484GenSource1664
end QiushiMatmul
