import QiushiPlane430GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane430GenNoModel (x : Fin 36 → Int) (hroot : plane430GenOccSys.RootHolds x) : False := by
  exact plane430GenLeaf0000 x hroot

end QiushiMatmul
