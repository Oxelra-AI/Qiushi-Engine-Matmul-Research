import QiushiPlane471LowerGenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane471LowerGenNoModel (x : Fin 6 → Int) (hroot : plane471LowerGenOccSys.RootHolds x) : False := by
  exact plane471LowerGenLeaf0000 x hroot

end QiushiMatmul
