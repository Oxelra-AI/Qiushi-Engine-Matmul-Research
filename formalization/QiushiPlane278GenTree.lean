import QiushiPlane278GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane278GenNoModel (x : Fin 24 → Int) (hroot : plane278GenOccSys.RootHolds x) : False := by
  exact plane278GenLeaf0000 x hroot

end QiushiMatmul
