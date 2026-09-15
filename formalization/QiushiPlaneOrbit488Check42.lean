import QiushiPlaneOrbit488Data

namespace QiushiMatmul.PlaneOrbit.Orbit488
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked42 : ∀ j : Fin 128,
    data.RowOK (data.ix (5376 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit488
