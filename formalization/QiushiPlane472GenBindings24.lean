import QiushiPlane472GenSources24
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane472GenBound0240 :
    QuotientRankAtLeast (spanCodes (plane472GenSourceBasis (240 : Fin 242))) (plane472GenSourceLb (240 : Fin 242)) := by
  rw [show plane472GenSourceBasis (240 : Fin 242) = [258, 128, 66, 32, 18, 10, 4, 1] from rfl,
      show plane472GenSourceLb (240 : Fin 242) = 9 from rfl]
  exact plane472GenSource0240
theorem plane472GenBound0241 :
    QuotientRankAtLeast (spanCodes (plane472GenSourceBasis (241 : Fin 242))) (plane472GenSourceLb (241 : Fin 242)) := by
  rw [show plane472GenSourceBasis (241 : Fin 242) = [258, 130, 64, 32, 16, 10, 4, 1] from rfl,
      show plane472GenSourceLb (241 : Fin 242) = 9 from rfl]
  exact plane472GenSource0241
end QiushiMatmul
