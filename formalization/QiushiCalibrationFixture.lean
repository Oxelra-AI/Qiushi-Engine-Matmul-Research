import QiushiCalibrationData
import QiushiConversion

open BigOperators

namespace QiushiMatmul.Calibration

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem fixture_entry_identity : ∀ a b c : Coord9,
    tensorEntry a b c = ∑ t : Fin 23,
      codeMat (fixtureACode t) a.1 a.2 * codeMat (fixtureBCode t) b.1 b.2 *
        codeMat (fixtureCCode t) c.1 c.2 := by
  decide +kernel

def fixture : TensorEntryDecomp 23 where
  A t := codeMat (fixtureACode t)
  B t := codeMat (fixtureBCode t)
  C t := codeMat (fixtureCCode t)
  entry_identity := fixture_entry_identity

end QiushiMatmul.Calibration
