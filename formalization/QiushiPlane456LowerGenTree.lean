import QiushiPlane456LowerGenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane456LowerGenNoModel (x : Fin 3 → Int) (hroot : plane456LowerGenOccSys.RootHolds x) : False := by
  exact plane456LowerGenLeaf0000 x hroot

end QiushiMatmul
