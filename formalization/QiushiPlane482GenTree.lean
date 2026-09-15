import QiushiPlane482GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane482GenNoModel (x : Fin 48 → Int) (hroot : plane482GenOccSys.RootHolds x) : False := by
  exact plane482GenLeaf0000 x hroot

end QiushiMatmul
