import QiushiPlane481GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane481GenNoModel (x : Fin 47 → Int) (hroot : plane481GenOccSys.RootHolds x) : False := by
  exact plane481GenLeaf0000 x hroot

end QiushiMatmul
