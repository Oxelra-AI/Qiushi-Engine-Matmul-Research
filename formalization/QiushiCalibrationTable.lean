import QiushiCalibrationTable000
import QiushiCalibrationTable001
import QiushiCalibrationTable002
import QiushiCalibrationTable003
import QiushiCalibrationTable004
import QiushiCalibrationTable005
import QiushiCalibrationTable006
import QiushiCalibrationTable007
import QiushiCalibrationTable008
import QiushiCalibrationTable009
import QiushiCalibrationTable010
import QiushiCalibrationTable011
import QiushiCalibrationTable012
import QiushiCalibrationTable013
import QiushiCalibrationTable014
import QiushiCalibrationTable015
import QiushiCalibrationTable016
import QiushiCalibrationTable017
import QiushiCalibrationTable018
import QiushiCalibrationTable019
import QiushiCalibrationTable020
import QiushiCalibrationTable021
import QiushiCalibrationTable022
import QiushiCalibrationTable023
import QiushiCalibrationTable024
import QiushiCalibrationTable025
import QiushiCalibrationTable026
import QiushiCalibrationTable027
import QiushiCalibrationTable028
import QiushiCalibrationTable029
import QiushiCalibrationTable030
import QiushiCalibrationTable031
import QiushiCalibrationTable032
import QiushiCalibrationTable033
import QiushiCalibrationTable034
import QiushiCalibrationTable035
import QiushiCalibrationTable036
import QiushiCalibrationTable037
import QiushiCalibrationTable038
import QiushiCalibrationTable039
import QiushiCalibrationTable040
import QiushiCalibrationTable041
import QiushiCalibrationTable042
import QiushiCalibrationTable043
import QiushiCalibrationTable044
import QiushiCalibrationTable045
import QiushiCalibrationTable046
import QiushiCalibrationTable047
import QiushiCalibrationTable048
import QiushiCalibrationTable049
import QiushiCalibrationTable050
import QiushiCalibrationTable051
import QiushiCalibrationTable052
import QiushiCalibrationTable053
import QiushiCalibrationTable054
import QiushiCalibrationTable055
import QiushiCalibrationTable056
import QiushiCalibrationTable057
import QiushiCalibrationTable058
import QiushiCalibrationTable059
import QiushiCalibrationTable060
import QiushiCalibrationTable061
import QiushiCalibrationTable062
import QiushiCalibrationTable063
import QiushiCalibrationTable064
import QiushiCalibrationTable065
import QiushiCalibrationTable066
import QiushiCalibrationTable067
import QiushiCalibrationTable068
import QiushiCalibrationTable069
import QiushiCalibrationTable070
import QiushiCalibrationTable071
import QiushiCalibrationTable072
import QiushiCalibrationTable073
import QiushiCalibrationTable074
import QiushiCalibrationTable075
import QiushiCalibrationTable076
import QiushiCalibrationTable077
import QiushiCalibrationTable078
import QiushiCalibrationTable079
import QiushiCalibrationTable080
import QiushiCalibrationTable081
import QiushiCalibrationTable082
import QiushiCalibrationTable083
import QiushiCalibrationTable084
import QiushiCalibrationTable085
import QiushiCalibrationTable086
import QiushiCalibrationTable087
import QiushiCalibrationTable088
import QiushiCalibrationTable089
import QiushiCalibrationTable090
import QiushiCalibrationTable091
import QiushiCalibrationTable092
import QiushiCalibrationTable093
import QiushiCalibrationTable094
import QiushiCalibrationTable095
import QiushiCalibrationTable096
import QiushiCalibrationTable097
import QiushiCalibrationTable098
import QiushiCalibrationTable099
import QiushiCalibrationTable100
import QiushiCalibrationTable101
import QiushiCalibrationTable102
import QiushiCalibrationTable103
import QiushiCalibrationTable104
import QiushiCalibrationTable105
import QiushiCalibrationTable106
import QiushiCalibrationTable107
import QiushiCalibrationTable108
import QiushiCalibrationTable109
import QiushiCalibrationTable110
import QiushiCalibrationTable111
import QiushiCalibrationTable112
import QiushiCalibrationTable113
import QiushiCalibrationTable114

namespace QiushiMatmul.Calibration

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

def tableChunks : Fin 115 → List TableRow := ![tableChunk000, tableChunk001, tableChunk002, tableChunk003, tableChunk004, tableChunk005, tableChunk006, tableChunk007, tableChunk008, tableChunk009, tableChunk010, tableChunk011, tableChunk012, tableChunk013, tableChunk014, tableChunk015, tableChunk016, tableChunk017, tableChunk018, tableChunk019, tableChunk020, tableChunk021, tableChunk022, tableChunk023, tableChunk024, tableChunk025, tableChunk026, tableChunk027, tableChunk028, tableChunk029, tableChunk030, tableChunk031, tableChunk032, tableChunk033, tableChunk034, tableChunk035, tableChunk036, tableChunk037, tableChunk038, tableChunk039, tableChunk040, tableChunk041, tableChunk042, tableChunk043, tableChunk044, tableChunk045, tableChunk046, tableChunk047, tableChunk048, tableChunk049, tableChunk050, tableChunk051, tableChunk052, tableChunk053, tableChunk054, tableChunk055, tableChunk056, tableChunk057, tableChunk058, tableChunk059, tableChunk060, tableChunk061, tableChunk062, tableChunk063, tableChunk064, tableChunk065, tableChunk066, tableChunk067, tableChunk068, tableChunk069, tableChunk070, tableChunk071, tableChunk072, tableChunk073, tableChunk074, tableChunk075, tableChunk076, tableChunk077, tableChunk078, tableChunk079, tableChunk080, tableChunk081, tableChunk082, tableChunk083, tableChunk084, tableChunk085, tableChunk086, tableChunk087, tableChunk088, tableChunk089, tableChunk090, tableChunk091, tableChunk092, tableChunk093, tableChunk094, tableChunk095, tableChunk096, tableChunk097, tableChunk098, tableChunk099, tableChunk100, tableChunk101, tableChunk102, tableChunk103, tableChunk104, tableChunk105, tableChunk106, tableChunk107, tableChunk108, tableChunk109, tableChunk110, tableChunk111, tableChunk112, tableChunk113, tableChunk114]

theorem tableChunks_check (i) : (tableChunks i).all TableRow.check = true := by
  fin_cases i
  · exact tableChunk000_check
  · exact tableChunk001_check
  · exact tableChunk002_check
  · exact tableChunk003_check
  · exact tableChunk004_check
  · exact tableChunk005_check
  · exact tableChunk006_check
  · exact tableChunk007_check
  · exact tableChunk008_check
  · exact tableChunk009_check
  · exact tableChunk010_check
  · exact tableChunk011_check
  · exact tableChunk012_check
  · exact tableChunk013_check
  · exact tableChunk014_check
  · exact tableChunk015_check
  · exact tableChunk016_check
  · exact tableChunk017_check
  · exact tableChunk018_check
  · exact tableChunk019_check
  · exact tableChunk020_check
  · exact tableChunk021_check
  · exact tableChunk022_check
  · exact tableChunk023_check
  · exact tableChunk024_check
  · exact tableChunk025_check
  · exact tableChunk026_check
  · exact tableChunk027_check
  · exact tableChunk028_check
  · exact tableChunk029_check
  · exact tableChunk030_check
  · exact tableChunk031_check
  · exact tableChunk032_check
  · exact tableChunk033_check
  · exact tableChunk034_check
  · exact tableChunk035_check
  · exact tableChunk036_check
  · exact tableChunk037_check
  · exact tableChunk038_check
  · exact tableChunk039_check
  · exact tableChunk040_check
  · exact tableChunk041_check
  · exact tableChunk042_check
  · exact tableChunk043_check
  · exact tableChunk044_check
  · exact tableChunk045_check
  · exact tableChunk046_check
  · exact tableChunk047_check
  · exact tableChunk048_check
  · exact tableChunk049_check
  · exact tableChunk050_check
  · exact tableChunk051_check
  · exact tableChunk052_check
  · exact tableChunk053_check
  · exact tableChunk054_check
  · exact tableChunk055_check
  · exact tableChunk056_check
  · exact tableChunk057_check
  · exact tableChunk058_check
  · exact tableChunk059_check
  · exact tableChunk060_check
  · exact tableChunk061_check
  · exact tableChunk062_check
  · exact tableChunk063_check
  · exact tableChunk064_check
  · exact tableChunk065_check
  · exact tableChunk066_check
  · exact tableChunk067_check
  · exact tableChunk068_check
  · exact tableChunk069_check
  · exact tableChunk070_check
  · exact tableChunk071_check
  · exact tableChunk072_check
  · exact tableChunk073_check
  · exact tableChunk074_check
  · exact tableChunk075_check
  · exact tableChunk076_check
  · exact tableChunk077_check
  · exact tableChunk078_check
  · exact tableChunk079_check
  · exact tableChunk080_check
  · exact tableChunk081_check
  · exact tableChunk082_check
  · exact tableChunk083_check
  · exact tableChunk084_check
  · exact tableChunk085_check
  · exact tableChunk086_check
  · exact tableChunk087_check
  · exact tableChunk088_check
  · exact tableChunk089_check
  · exact tableChunk090_check
  · exact tableChunk091_check
  · exact tableChunk092_check
  · exact tableChunk093_check
  · exact tableChunk094_check
  · exact tableChunk095_check
  · exact tableChunk096_check
  · exact tableChunk097_check
  · exact tableChunk098_check
  · exact tableChunk099_check
  · exact tableChunk100_check
  · exact tableChunk101_check
  · exact tableChunk102_check
  · exact tableChunk103_check
  · exact tableChunk104_check
  · exact tableChunk105_check
  · exact tableChunk106_check
  · exact tableChunk107_check
  · exact tableChunk108_check
  · exact tableChunk109_check
  · exact tableChunk110_check
  · exact tableChunk111_check
  · exact tableChunk112_check
  · exact tableChunk113_check
  · exact tableChunk114_check

def table : List TableRow := (List.ofFn tableChunks).flatten

set_option maxRecDepth 200000 in
set_option maxHeartbeats 24000000 in
theorem table_length : table.length = 29210 := by decide +kernel

theorem table_controls (row : TableRow) (hr : row ∈ table) : row.ControlsHold := by
  obtain ⟨rs, hrs, hrow⟩ := List.mem_flatten.mp hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrs
  exact controlsHold_of_all_check _ (tableChunks_check i) row hrow

/-- Numeric-mask order used by the independent geometric catalogue. -/
def orderedTable : List TableRow := table.mergeSort (fun a b => decide (a.mask ≤ b.mask))

theorem orderedTable_length : orderedTable.length = 29210 := by
  simpa only [orderedTable, List.length_mergeSort] using table_length

theorem orderedTable_controls (row : TableRow) (hr : row ∈ orderedTable) : row.ControlsHold :=
  table_controls row (List.mem_mergeSort.mp hr)

def tableRow (j : Fin 29210) : TableRow :=
  orderedTable.get ⟨j.val, by rw [orderedTable_length]; exact j.isLt⟩

theorem tableRow_controls (j : Fin 29210) : (tableRow j).ControlsHold :=
  orderedTable_controls _ (List.get_mem _ _)

end QiushiMatmul.Calibration
