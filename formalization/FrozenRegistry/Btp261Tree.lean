import FrozenRegistry.Btp261Leaves000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane261BtpGenNoModel (x : Fin 31 → Int) (hroot : plane261BtpGenOccSys.RootHolds x) : False := by
  exact plane261BtpGenLeaf0000 x hroot

end QiushiMatmul
