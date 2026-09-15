import QiushiPlane419GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane419GenNoModel (x : Fin 24 → Int) (hroot : plane419GenOccSys.RootHolds x) : False := by
  exact plane419GenLeaf0000 x hroot

end QiushiMatmul
