import QiushiPlaneOrbit488Data

namespace QiushiMatmul.PlaneOrbit.Orbit488
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked34 : ∀ j : Fin 128,
    data.RowOK (data.ix (4352 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit488
