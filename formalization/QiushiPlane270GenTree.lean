import QiushiPlane270GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane270GenNoModel (x : Fin 11 → Int) (hroot : plane270GenOccSys.RootHolds x) : False := by
  exact plane270GenLeaf0000 x hroot

end QiushiMatmul
