import QiushiPlane413GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane413GenNoModel (x : Fin 21 → Int) (hroot : plane413GenOccSys.RootHolds x) : False := by
  exact plane413GenLeaf0000 x hroot

end QiushiMatmul
