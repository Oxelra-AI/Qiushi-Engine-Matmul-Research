import QiushiPlane338GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane338GenNoModel (x : Fin 16 → Int) (hroot : plane338GenOccSys.RootHolds x) : False := by
  exact plane338GenLeaf0000 x hroot

end QiushiMatmul
