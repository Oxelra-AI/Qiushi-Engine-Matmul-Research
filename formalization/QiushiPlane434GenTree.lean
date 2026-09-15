import QiushiPlane434GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane434GenNoModel (x : Fin 37 → Int) (hroot : plane434GenOccSys.RootHolds x) : False := by
  exact plane434GenLeaf0000 x hroot

end QiushiMatmul
