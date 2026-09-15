import FrozenRegistry.Btp263Leaves000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane263BtpGenNoModel (x : Fin 31 → Int) (hroot : plane263BtpGenOccSys.RootHolds x) : False := by
  exact plane263BtpGenLeaf0000 x hroot

end QiushiMatmul
