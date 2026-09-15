import QiushiPlaneOrbit487Data

namespace QiushiMatmul.PlaneOrbit.Orbit487
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked1 : ∀ j : Fin 128,
    data.RowOK (data.ix (128 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit487
