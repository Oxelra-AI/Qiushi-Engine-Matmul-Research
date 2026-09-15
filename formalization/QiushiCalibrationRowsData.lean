import QiushiCalibrationRowsOrder

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 200000
set_option maxHeartbeats 80000000

/-- Ascending numeric mask order, independent of every orbit's L0 labels. -/
def allData : List RowData := data000 ++ (data001 ++ (data002 ++ (data003 ++ (data004 ++ (data005 ++ (data006 ++ (data007 ++ (data008 ++ (data009 ++ (data010 ++ (data011 ++ (data012 ++ (data013 ++ (data014 ++ (data015 ++ (data016 ++ (data017 ++ (data018 ++ (data019 ++ (data020 ++ (data021 ++ (data022 ++ (data023 ++ (data024 ++ (data025 ++ (data026 ++ (data027 ++ (data028 ++ (data029 ++ (data030 ++ (data031 ++ (data032 ++ (data033 ++ (data034 ++ (data035 ++ (data036 ++ (data037 ++ (data038 ++ (data039 ++ (data040 ++ (data041 ++ (data042 ++ (data043 ++ (data044 ++ (data045 ++ (data046 ++ (data047 ++ (data048 ++ (data049 ++ (data050 ++ (data051 ++ (data052 ++ (data053 ++ (data054 ++ (data055 ++ (data056 ++ (data057)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem append_length_eq {a b : List RowData} {n m : Nat}
    (ha : a.length = n) (hb : b.length = m) : (a ++ b).length = n + m :=
  List.length_append.trans (congrArg₂ Nat.add ha hb)

private theorem append_valid {a b : List RowData}
    (ha : ∀ d ∈ a, d.Valid) (hb : ∀ d ∈ b, d.Valid) : ∀ d ∈ a ++ b, d.Valid := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · exact ha d h
  · exact hb d h

private theorem append_mask_map {a b : List RowData} {c d : List Nat}
    (ha : a.map RowData.mask = c) (hb : b.map RowData.mask = d) :
    (a ++ b).map RowData.mask = c ++ d :=
  (List.map_append ..).trans (congrArg₂ List.append ha hb)

theorem allData_length : allData.length = 29210 :=
  append_length_eq length000 (append_length_eq length001 (append_length_eq length002 (append_length_eq length003 (append_length_eq length004 (append_length_eq length005 (append_length_eq length006 (append_length_eq length007 (append_length_eq length008 (append_length_eq length009 (append_length_eq length010 (append_length_eq length011 (append_length_eq length012 (append_length_eq length013 (append_length_eq length014 (append_length_eq length015 (append_length_eq length016 (append_length_eq length017 (append_length_eq length018 (append_length_eq length019 (append_length_eq length020 (append_length_eq length021 (append_length_eq length022 (append_length_eq length023 (append_length_eq length024 (append_length_eq length025 (append_length_eq length026 (append_length_eq length027 (append_length_eq length028 (append_length_eq length029 (append_length_eq length030 (append_length_eq length031 (append_length_eq length032 (append_length_eq length033 (append_length_eq length034 (append_length_eq length035 (append_length_eq length036 (append_length_eq length037 (append_length_eq length038 (append_length_eq length039 (append_length_eq length040 (append_length_eq length041 (append_length_eq length042 (append_length_eq length043 (append_length_eq length044 (append_length_eq length045 (append_length_eq length046 (append_length_eq length047 (append_length_eq length048 (append_length_eq length049 (append_length_eq length050 (append_length_eq length051 (append_length_eq length052 (append_length_eq length053 (append_length_eq length054 (append_length_eq length055 (append_length_eq length056 (length057)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem allData_valid : ∀ d ∈ allData, d.Valid :=
  append_valid valid000 (append_valid valid001 (append_valid valid002 (append_valid valid003 (append_valid valid004 (append_valid valid005 (append_valid valid006 (append_valid valid007 (append_valid valid008 (append_valid valid009 (append_valid valid010 (append_valid valid011 (append_valid valid012 (append_valid valid013 (append_valid valid014 (append_valid valid015 (append_valid valid016 (append_valid valid017 (append_valid valid018 (append_valid valid019 (append_valid valid020 (append_valid valid021 (append_valid valid022 (append_valid valid023 (append_valid valid024 (append_valid valid025 (append_valid valid026 (append_valid valid027 (append_valid valid028 (append_valid valid029 (append_valid valid030 (append_valid valid031 (append_valid valid032 (append_valid valid033 (append_valid valid034 (append_valid valid035 (append_valid valid036 (append_valid valid037 (append_valid valid038 (append_valid valid039 (append_valid valid040 (append_valid valid041 (append_valid valid042 (append_valid valid043 (append_valid valid044 (append_valid valid045 (append_valid valid046 (append_valid valid047 (append_valid valid048 (append_valid valid049 (append_valid valid050 (append_valid valid051 (append_valid valid052 (append_valid valid053 (append_valid valid054 (append_valid valid055 (append_valid valid056 (valid057)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem allData_masks : allData.map RowData.mask = maskSuffix000 :=
  append_mask_map (rfl : data000.map RowData.mask = data000.map RowData.mask) (append_mask_map (rfl : data001.map RowData.mask = data001.map RowData.mask) (append_mask_map (rfl : data002.map RowData.mask = data002.map RowData.mask) (append_mask_map (rfl : data003.map RowData.mask = data003.map RowData.mask) (append_mask_map (rfl : data004.map RowData.mask = data004.map RowData.mask) (append_mask_map (rfl : data005.map RowData.mask = data005.map RowData.mask) (append_mask_map (rfl : data006.map RowData.mask = data006.map RowData.mask) (append_mask_map (rfl : data007.map RowData.mask = data007.map RowData.mask) (append_mask_map (rfl : data008.map RowData.mask = data008.map RowData.mask) (append_mask_map (rfl : data009.map RowData.mask = data009.map RowData.mask) (append_mask_map (rfl : data010.map RowData.mask = data010.map RowData.mask) (append_mask_map (rfl : data011.map RowData.mask = data011.map RowData.mask) (append_mask_map (rfl : data012.map RowData.mask = data012.map RowData.mask) (append_mask_map (rfl : data013.map RowData.mask = data013.map RowData.mask) (append_mask_map (rfl : data014.map RowData.mask = data014.map RowData.mask) (append_mask_map (rfl : data015.map RowData.mask = data015.map RowData.mask) (append_mask_map (rfl : data016.map RowData.mask = data016.map RowData.mask) (append_mask_map (rfl : data017.map RowData.mask = data017.map RowData.mask) (append_mask_map (rfl : data018.map RowData.mask = data018.map RowData.mask) (append_mask_map (rfl : data019.map RowData.mask = data019.map RowData.mask) (append_mask_map (rfl : data020.map RowData.mask = data020.map RowData.mask) (append_mask_map (rfl : data021.map RowData.mask = data021.map RowData.mask) (append_mask_map (rfl : data022.map RowData.mask = data022.map RowData.mask) (append_mask_map (rfl : data023.map RowData.mask = data023.map RowData.mask) (append_mask_map (rfl : data024.map RowData.mask = data024.map RowData.mask) (append_mask_map (rfl : data025.map RowData.mask = data025.map RowData.mask) (append_mask_map (rfl : data026.map RowData.mask = data026.map RowData.mask) (append_mask_map (rfl : data027.map RowData.mask = data027.map RowData.mask) (append_mask_map (rfl : data028.map RowData.mask = data028.map RowData.mask) (append_mask_map (rfl : data029.map RowData.mask = data029.map RowData.mask) (append_mask_map (rfl : data030.map RowData.mask = data030.map RowData.mask) (append_mask_map (rfl : data031.map RowData.mask = data031.map RowData.mask) (append_mask_map (rfl : data032.map RowData.mask = data032.map RowData.mask) (append_mask_map (rfl : data033.map RowData.mask = data033.map RowData.mask) (append_mask_map (rfl : data034.map RowData.mask = data034.map RowData.mask) (append_mask_map (rfl : data035.map RowData.mask = data035.map RowData.mask) (append_mask_map (rfl : data036.map RowData.mask = data036.map RowData.mask) (append_mask_map (rfl : data037.map RowData.mask = data037.map RowData.mask) (append_mask_map (rfl : data038.map RowData.mask = data038.map RowData.mask) (append_mask_map (rfl : data039.map RowData.mask = data039.map RowData.mask) (append_mask_map (rfl : data040.map RowData.mask = data040.map RowData.mask) (append_mask_map (rfl : data041.map RowData.mask = data041.map RowData.mask) (append_mask_map (rfl : data042.map RowData.mask = data042.map RowData.mask) (append_mask_map (rfl : data043.map RowData.mask = data043.map RowData.mask) (append_mask_map (rfl : data044.map RowData.mask = data044.map RowData.mask) (append_mask_map (rfl : data045.map RowData.mask = data045.map RowData.mask) (append_mask_map (rfl : data046.map RowData.mask = data046.map RowData.mask) (append_mask_map (rfl : data047.map RowData.mask = data047.map RowData.mask) (append_mask_map (rfl : data048.map RowData.mask = data048.map RowData.mask) (append_mask_map (rfl : data049.map RowData.mask = data049.map RowData.mask) (append_mask_map (rfl : data050.map RowData.mask = data050.map RowData.mask) (append_mask_map (rfl : data051.map RowData.mask = data051.map RowData.mask) (append_mask_map (rfl : data052.map RowData.mask = data052.map RowData.mask) (append_mask_map (rfl : data053.map RowData.mask = data053.map RowData.mask) (append_mask_map (rfl : data054.map RowData.mask = data054.map RowData.mask) (append_mask_map (rfl : data055.map RowData.mask = data055.map RowData.mask) (append_mask_map (rfl : data056.map RowData.mask = data056.map RowData.mask) ((rfl : data057.map RowData.mask = maskSuffix057))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem allData_sorted : (allData.map RowData.mask).IsChain (· < ·) :=
  allData_masks.symm ▸ suffixSorted000

def standardRows : Fin 29210 → Row standardCoordinates :=
  catalogueRows allData allData_length allData_valid

theorem standardRows_distinct : Function.Injective
    (fun i j => (standardRows i).mask.testBit j.val : Fin 29210 → Fin 127 → Bool) :=
  catalogueRows_distinct allData allData_length allData_valid allData_sorted

theorem standardRows_complete (U : Submodule F2 Mat3)
    (hWU : spanCodes [256, 128] < U) (hU : U < ⊤) :
    ∃! i, (standardRows i).space = U :=
  catalogueRows_complete allData allData_length allData_valid allData_sorted U hWU hU

end QiushiMatmul.CalibrationRows
