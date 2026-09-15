import QiushiPlaneOrbit490Data

namespace QiushiMatmul.PlaneOrbit.Orbit490
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked12 : ∀ j : Fin 128,
    data.RowOK (data.ix (1536 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit490
