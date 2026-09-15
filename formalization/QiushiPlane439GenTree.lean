import QiushiPlane439GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane439GenNoModel (x : Fin 13 → Int) (hroot : plane439GenOccSys.RootHolds x) : False := by
  exact plane439GenLeaf0000 x hroot

end QiushiMatmul
