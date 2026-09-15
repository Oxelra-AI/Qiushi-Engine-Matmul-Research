import QiushiPlane483GenSources11
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane483GenBound0110 :
    QuotientRankAtLeast (spanCodes (plane483GenSourceBasis (110 : Fin 112))) (plane483GenSourceLb (110 : Fin 112)) := by
  rw [show plane483GenSourceBasis (110 : Fin 112) = [260, 160, 98, 18, 10, 1] from rfl,
      show plane483GenSourceLb (110 : Fin 112) = 12 from rfl]
  exact plane483GenSource0110
theorem plane483GenBound0111 :
    QuotientRankAtLeast (spanCodes (plane483GenSourceBasis (111 : Fin 112))) (plane483GenSourceLb (111 : Fin 112)) := by
  rw [show plane483GenSourceBasis (111 : Fin 112) = [260, 132, 68, 36, 16, 10, 1] from rfl,
      show plane483GenSourceLb (111 : Fin 112) = 12 from rfl]
  exact plane483GenSource0111
end QiushiMatmul
