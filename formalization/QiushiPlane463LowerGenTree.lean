import QiushiPlane463LowerGenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane463LowerGenNoModel (x : Fin 6 → Int) (hroot : plane463LowerGenOccSys.RootHolds x) : False := by
  exact plane463LowerGenLeaf0000 x hroot

end QiushiMatmul
