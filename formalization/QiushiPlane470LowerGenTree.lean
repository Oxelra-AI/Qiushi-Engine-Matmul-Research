import QiushiPlane470LowerGenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane470LowerGenNoModel (x : Fin 5 → Int) (hroot : plane470LowerGenOccSys.RootHolds x) : False := by
  exact plane470LowerGenLeaf0000 x hroot

end QiushiMatmul
