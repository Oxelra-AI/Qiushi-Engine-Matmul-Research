import QiushiPlane484GenSources100
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane484GenBound1000 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1000 : Fin 1665))) (plane484GenSourceLb (1000 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1000 : Fin 1665) = [384, 67, 35, 19, 10, 5] from rfl,
      show plane484GenSourceLb (1000 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1000
theorem plane484GenBound1001 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1001 : Fin 1665))) (plane484GenSourceLb (1001 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1001 : Fin 1665) = [256, 129, 66, 35, 19, 10, 5] from rfl,
      show plane484GenSourceLb (1001 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1001
theorem plane484GenBound1002 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1002 : Fin 1665))) (plane484GenSourceLb (1002 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1002 : Fin 1665) = [257, 128, 66, 35, 19, 10, 5] from rfl,
      show plane484GenSourceLb (1002 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1002
theorem plane484GenBound1003 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1003 : Fin 1665))) (plane484GenSourceLb (1003 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1003 : Fin 1665) = [290, 129, 66, 19, 10, 4] from rfl,
      show plane484GenSourceLb (1003 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1003
theorem plane484GenBound1004 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1004 : Fin 1665))) (plane484GenSourceLb (1004 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1004 : Fin 1665) = [385, 65, 33, 19, 10, 4] from rfl,
      show plane484GenSourceLb (1004 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1004
theorem plane484GenBound1005 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1005 : Fin 1665))) (plane484GenSourceLb (1005 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1005 : Fin 1665) = [258, 129, 65, 35, 19, 10, 4] from rfl,
      show plane484GenSourceLb (1005 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1005
theorem plane484GenBound1006 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1006 : Fin 1665))) (plane484GenSourceLb (1006 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1006 : Fin 1665) = [257, 128, 67, 35, 19, 10, 4] from rfl,
      show plane484GenSourceLb (1006 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1006
theorem plane484GenBound1007 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1007 : Fin 1665))) (plane484GenSourceLb (1007 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1007 : Fin 1665) = [322, 129, 34, 19, 10, 4] from rfl,
      show plane484GenSourceLb (1007 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1007
theorem plane484GenBound1008 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1008 : Fin 1665))) (plane484GenSourceLb (1008 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1008 : Fin 1665) = [291, 129, 64, 19, 10, 7] from rfl,
      show plane484GenSourceLb (1008 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1008
theorem plane484GenBound1009 :
    QuotientRankAtLeast (spanCodes (plane484GenSourceBasis (1009 : Fin 1665))) (plane484GenSourceLb (1009 : Fin 1665)) := by
  rw [show plane484GenSourceBasis (1009 : Fin 1665) = [288, 128, 66, 19, 10, 7] from rfl,
      show plane484GenSourceLb (1009 : Fin 1665) = 14 from rfl]
  exact plane484GenSource1009
end QiushiMatmul
