import QiushiPlaneOrbit481Data

namespace QiushiMatmul.PlaneOrbit.Orbit481
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked14 : ∀ j : Fin 128,
    data.RowOK (data.ix (1792 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit481
