import QiushiPlane298GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane298GenNoModel (x : Fin 13 → Int) (hroot : plane298GenOccSys.RootHolds x) : False := by
  exact plane298GenLeaf0000 x hroot

end QiushiMatmul
