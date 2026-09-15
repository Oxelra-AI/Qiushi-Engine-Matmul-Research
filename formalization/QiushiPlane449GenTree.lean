import QiushiPlane449GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane449GenNoModel (x : Fin 15 → Int) (hroot : plane449GenOccSys.RootHolds x) : False := by
  exact plane449GenLeaf0000 x hroot

end QiushiMatmul
