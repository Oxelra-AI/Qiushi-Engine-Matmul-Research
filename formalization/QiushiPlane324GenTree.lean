import QiushiPlane324GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane324GenNoModel (x : Fin 14 → Int) (hroot : plane324GenOccSys.RootHolds x) : False := by
  exact plane324GenLeaf0000 x hroot

end QiushiMatmul
