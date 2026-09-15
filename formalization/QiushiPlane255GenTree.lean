import QiushiPlane255GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane255GenNoModel (x : Fin 14 → Int) (hroot : plane255GenOccSys.RootHolds x) : False := by
  exact plane255GenLeaf0000 x hroot

end QiushiMatmul
