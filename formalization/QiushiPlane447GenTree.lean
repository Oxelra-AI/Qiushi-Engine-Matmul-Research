import QiushiPlane447GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane447GenNoModel (x : Fin 13 → Int) (hroot : plane447GenOccSys.RootHolds x) : False := by
  exact plane447GenLeaf0000 x hroot

end QiushiMatmul
