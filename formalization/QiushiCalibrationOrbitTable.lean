import QiushiCalibrationOrbitChunk000
import QiushiCalibrationOrbitChunk001
import QiushiCalibrationOrbitChunk002
import QiushiCalibrationOrbitChunk003
import QiushiCalibrationOrbitChunk004
import QiushiCalibrationOrbitChunk005
import QiushiCalibrationOrbitChunk006
import QiushiCalibrationOrbitChunk007
import QiushiCalibrationOrbitChunk008
import QiushiCalibrationOrbitChunk009
import QiushiCalibrationOrbitChunk010
import QiushiCalibrationOrbitChunk011
import QiushiCalibrationOrbitChunk012
import QiushiCalibrationOrbitChunk013
import QiushiCalibrationOrbitChunk014
import QiushiCalibrationOrbitChunk015
import QiushiCalibrationOrbitChunk016
import QiushiCalibrationOrbitChunk017
import QiushiCalibrationOrbitChunk018
import QiushiCalibrationOrbitChunk019
import QiushiCalibrationOrbitChunk020
import QiushiCalibrationOrbitChunk021
import QiushiCalibrationOrbitChunk022
import QiushiCalibrationOrbitChunk023
import QiushiCalibrationOrbitChunk024
import QiushiCalibrationOrbitChunk025
import QiushiCalibrationOrbitChunk026
import QiushiCalibrationOrbitChunk027
import QiushiCalibrationOrbitChunk028
import QiushiCalibrationOrbitChunk029
import QiushiCalibrationOrbitChunk030
import QiushiCalibrationOrbitChunk031
import QiushiCalibrationOrbitChunk032
import QiushiCalibrationOrbitChunk033
import QiushiCalibrationOrbitChunk034
import QiushiCalibrationOrbitChunk035
import QiushiCalibrationOrbitChunk036
import QiushiCalibrationOrbitChunk037
import QiushiCalibrationOrbitChunk038
import QiushiCalibrationOrbitChunk039
import QiushiCalibrationOrbitChunk040
import QiushiCalibrationOrbitChunk041
import QiushiCalibrationOrbitChunk042
import QiushiCalibrationOrbitChunk043
import QiushiCalibrationOrbitChunk044
import QiushiCalibrationOrbitChunk045
import QiushiCalibrationOrbitChunk046
import QiushiCalibrationOrbitChunk047
import QiushiCalibrationOrbitChunk048
import QiushiCalibrationOrbitChunk049
import QiushiCalibrationOrbitChunk050
import QiushiCalibrationOrbitChunk051
import QiushiCalibrationOrbitChunk052
import QiushiCalibrationOrbitChunk053
import QiushiCalibrationOrbitChunk054
import QiushiCalibrationOrbitChunk055
import QiushiCalibrationOrbitChunk056
import QiushiCalibrationOrbitChunk057
import QiushiCalibrationOrbitChunk058
import QiushiCalibrationOrbitChunk059
import QiushiCalibrationOrbitChunk060
import QiushiCalibrationOrbitChunk061
import QiushiCalibrationOrbitChunk062
import QiushiCalibrationOrbitChunk063
import QiushiCalibrationOrbitChunk064
import QiushiCalibrationOrbitChunk065
import QiushiCalibrationOrbitChunk066
import QiushiCalibrationOrbitChunk067
import QiushiCalibrationOrbitChunk068
import QiushiCalibrationOrbitChunk069
import QiushiCalibrationOrbitChunk070
import QiushiCalibrationOrbitChunk071
import QiushiCalibrationOrbitChunk072
import QiushiCalibrationOrbitChunk073
import QiushiCalibrationOrbitChunk074
import QiushiCalibrationOrbitChunk075
import QiushiCalibrationOrbitChunk076
import QiushiCalibrationOrbitChunk077
import QiushiCalibrationOrbitChunk078
import QiushiCalibrationOrbitChunk079
import QiushiCalibrationOrbitChunk080
import QiushiCalibrationOrbitChunk081
import QiushiCalibrationOrbitChunk082
import QiushiCalibrationOrbitChunk083
import QiushiCalibrationOrbitChunk084
import QiushiCalibrationOrbitChunk085
import QiushiCalibrationOrbitChunk086
import QiushiCalibrationOrbitChunk087
import QiushiCalibrationOrbitChunk088
import QiushiCalibrationOrbitChunk089
import QiushiCalibrationOrbitChunk090
import QiushiCalibrationOrbitChunk091
import QiushiCalibrationOrbitChunk092
import QiushiCalibrationOrbitChunk093
import QiushiCalibrationOrbitChunk094
import QiushiCalibrationOrbitChunk095
import QiushiCalibrationOrbitChunk096
import QiushiCalibrationOrbitChunk097
import QiushiCalibrationOrbitChunk098
import QiushiCalibrationOrbitChunk099
import QiushiCalibrationOrbitChunk100
import QiushiCalibrationOrbitChunk101
import QiushiCalibrationOrbitChunk102
import QiushiCalibrationOrbitChunk103
import QiushiCalibrationOrbitChunk104
import QiushiCalibrationOrbitChunk105
import QiushiCalibrationOrbitChunk106
import QiushiCalibrationOrbitChunk107
import QiushiCalibrationOrbitChunk108
import QiushiCalibrationOrbitChunk109
import QiushiCalibrationOrbitChunk110
import QiushiCalibrationOrbitChunk111
import QiushiCalibrationOrbitChunk112
import QiushiCalibrationOrbitChunk113
import QiushiCalibrationOrbitChunk114
import QiushiCalibrationTable
import QiushiCalibrationSort

namespace QiushiMatmul.Calibration

set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

def orbitRecordChunks : Fin 115 → List OrbitRecord := ![orbitRecords000, orbitRecords001, orbitRecords002, orbitRecords003, orbitRecords004, orbitRecords005, orbitRecords006, orbitRecords007, orbitRecords008, orbitRecords009, orbitRecords010, orbitRecords011, orbitRecords012, orbitRecords013, orbitRecords014, orbitRecords015, orbitRecords016, orbitRecords017, orbitRecords018, orbitRecords019, orbitRecords020, orbitRecords021, orbitRecords022, orbitRecords023, orbitRecords024, orbitRecords025, orbitRecords026, orbitRecords027, orbitRecords028, orbitRecords029, orbitRecords030, orbitRecords031, orbitRecords032, orbitRecords033, orbitRecords034, orbitRecords035, orbitRecords036, orbitRecords037, orbitRecords038, orbitRecords039, orbitRecords040, orbitRecords041, orbitRecords042, orbitRecords043, orbitRecords044, orbitRecords045, orbitRecords046, orbitRecords047, orbitRecords048, orbitRecords049, orbitRecords050, orbitRecords051, orbitRecords052, orbitRecords053, orbitRecords054, orbitRecords055, orbitRecords056, orbitRecords057, orbitRecords058, orbitRecords059, orbitRecords060, orbitRecords061, orbitRecords062, orbitRecords063, orbitRecords064, orbitRecords065, orbitRecords066, orbitRecords067, orbitRecords068, orbitRecords069, orbitRecords070, orbitRecords071, orbitRecords072, orbitRecords073, orbitRecords074, orbitRecords075, orbitRecords076, orbitRecords077, orbitRecords078, orbitRecords079, orbitRecords080, orbitRecords081, orbitRecords082, orbitRecords083, orbitRecords084, orbitRecords085, orbitRecords086, orbitRecords087, orbitRecords088, orbitRecords089, orbitRecords090, orbitRecords091, orbitRecords092, orbitRecords093, orbitRecords094, orbitRecords095, orbitRecords096, orbitRecords097, orbitRecords098, orbitRecords099, orbitRecords100, orbitRecords101, orbitRecords102, orbitRecords103, orbitRecords104, orbitRecords105, orbitRecords106, orbitRecords107, orbitRecords108, orbitRecords109, orbitRecords110, orbitRecords111, orbitRecords112, orbitRecords113, orbitRecords114]

theorem orbitRecordChunks_check (i) :
    (orbitRecordChunks i).all (fun r => decide r.Valid) = true := by
  fin_cases i
  · exact orbitRecords000_check
  · exact orbitRecords001_check
  · exact orbitRecords002_check
  · exact orbitRecords003_check
  · exact orbitRecords004_check
  · exact orbitRecords005_check
  · exact orbitRecords006_check
  · exact orbitRecords007_check
  · exact orbitRecords008_check
  · exact orbitRecords009_check
  · exact orbitRecords010_check
  · exact orbitRecords011_check
  · exact orbitRecords012_check
  · exact orbitRecords013_check
  · exact orbitRecords014_check
  · exact orbitRecords015_check
  · exact orbitRecords016_check
  · exact orbitRecords017_check
  · exact orbitRecords018_check
  · exact orbitRecords019_check
  · exact orbitRecords020_check
  · exact orbitRecords021_check
  · exact orbitRecords022_check
  · exact orbitRecords023_check
  · exact orbitRecords024_check
  · exact orbitRecords025_check
  · exact orbitRecords026_check
  · exact orbitRecords027_check
  · exact orbitRecords028_check
  · exact orbitRecords029_check
  · exact orbitRecords030_check
  · exact orbitRecords031_check
  · exact orbitRecords032_check
  · exact orbitRecords033_check
  · exact orbitRecords034_check
  · exact orbitRecords035_check
  · exact orbitRecords036_check
  · exact orbitRecords037_check
  · exact orbitRecords038_check
  · exact orbitRecords039_check
  · exact orbitRecords040_check
  · exact orbitRecords041_check
  · exact orbitRecords042_check
  · exact orbitRecords043_check
  · exact orbitRecords044_check
  · exact orbitRecords045_check
  · exact orbitRecords046_check
  · exact orbitRecords047_check
  · exact orbitRecords048_check
  · exact orbitRecords049_check
  · exact orbitRecords050_check
  · exact orbitRecords051_check
  · exact orbitRecords052_check
  · exact orbitRecords053_check
  · exact orbitRecords054_check
  · exact orbitRecords055_check
  · exact orbitRecords056_check
  · exact orbitRecords057_check
  · exact orbitRecords058_check
  · exact orbitRecords059_check
  · exact orbitRecords060_check
  · exact orbitRecords061_check
  · exact orbitRecords062_check
  · exact orbitRecords063_check
  · exact orbitRecords064_check
  · exact orbitRecords065_check
  · exact orbitRecords066_check
  · exact orbitRecords067_check
  · exact orbitRecords068_check
  · exact orbitRecords069_check
  · exact orbitRecords070_check
  · exact orbitRecords071_check
  · exact orbitRecords072_check
  · exact orbitRecords073_check
  · exact orbitRecords074_check
  · exact orbitRecords075_check
  · exact orbitRecords076_check
  · exact orbitRecords077_check
  · exact orbitRecords078_check
  · exact orbitRecords079_check
  · exact orbitRecords080_check
  · exact orbitRecords081_check
  · exact orbitRecords082_check
  · exact orbitRecords083_check
  · exact orbitRecords084_check
  · exact orbitRecords085_check
  · exact orbitRecords086_check
  · exact orbitRecords087_check
  · exact orbitRecords088_check
  · exact orbitRecords089_check
  · exact orbitRecords090_check
  · exact orbitRecords091_check
  · exact orbitRecords092_check
  · exact orbitRecords093_check
  · exact orbitRecords094_check
  · exact orbitRecords095_check
  · exact orbitRecords096_check
  · exact orbitRecords097_check
  · exact orbitRecords098_check
  · exact orbitRecords099_check
  · exact orbitRecords100_check
  · exact orbitRecords101_check
  · exact orbitRecords102_check
  · exact orbitRecords103_check
  · exact orbitRecords104_check
  · exact orbitRecords105_check
  · exact orbitRecords106_check
  · exact orbitRecords107_check
  · exact orbitRecords108_check
  · exact orbitRecords109_check
  · exact orbitRecords110_check
  · exact orbitRecords111_check
  · exact orbitRecords112_check
  · exact orbitRecords113_check
  · exact orbitRecords114_check

def allOrbitRecords : List OrbitRecord := (List.ofFn orbitRecordChunks).flatten

theorem allOrbitRecords_length : allOrbitRecords.length = 29210 := by decide +kernel

theorem allOrbitRecords_valid (r : OrbitRecord) (hr : r ∈ allOrbitRecords) : r.Valid := by
  obtain ⟨rs, hrs, hrow⟩ := List.mem_flatten.mp hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrs
  exact orbitRecords_valid _ (orbitRecordChunks_check i) r hrow

/-- Every packed label is bound to the already checked public table. -/
theorem allOrbitRecords_table : allOrbitRecords.map OrbitRecord.row = orderedTable := by
  unfold orderedTable
  rw [← sortFuel_eq _ table.length table (le_refl _)]
  decide +kernel

def orbitRecordAt (j : Fin 29210) : OrbitRecord :=
  allOrbitRecords.get ⟨j.val, by rw [allOrbitRecords_length]; exact j.isLt⟩

theorem orbitRecordAt_valid (j : Fin 29210) : (orbitRecordAt j).Valid :=
  allOrbitRecords_valid _ (List.get_mem _ _)

theorem orbitRecordAt_row (j : Fin 29210) : (orbitRecordAt j).row = tableRow j := by
  have h := congrArg (fun xs : List TableRow => xs[j.val]?) allOrbitRecords_table
  have hl : j.val < allOrbitRecords.length := by rw [allOrbitRecords_length]; exact j.isLt
  have hr : j.val < orderedTable.length := by rw [orderedTable_length]; exact j.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem hl,
    List.getElem?_eq_getElem hr, Option.map_some, Option.some.injEq] at h
  exact h

end QiushiMatmul.Calibration
