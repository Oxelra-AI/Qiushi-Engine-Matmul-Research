import QiushiPlane275GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane275GenNoModel (x : Fin 9 → Int) (hroot : plane275GenOccSys.RootHolds x) : False := by
  exact plane275GenLeaf0000 x hroot

end QiushiMatmul
