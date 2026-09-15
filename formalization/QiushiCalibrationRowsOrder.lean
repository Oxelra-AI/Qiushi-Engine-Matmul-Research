import QiushiCalibrationRowsChunk000
import QiushiCalibrationRowsChunk001
import QiushiCalibrationRowsChunk002
import QiushiCalibrationRowsChunk003
import QiushiCalibrationRowsChunk004
import QiushiCalibrationRowsChunk005
import QiushiCalibrationRowsChunk006
import QiushiCalibrationRowsChunk007
import QiushiCalibrationRowsChunk008
import QiushiCalibrationRowsChunk009
import QiushiCalibrationRowsChunk010
import QiushiCalibrationRowsChunk011
import QiushiCalibrationRowsChunk012
import QiushiCalibrationRowsChunk013
import QiushiCalibrationRowsChunk014
import QiushiCalibrationRowsChunk015
import QiushiCalibrationRowsChunk016
import QiushiCalibrationRowsChunk017
import QiushiCalibrationRowsChunk018
import QiushiCalibrationRowsChunk019
import QiushiCalibrationRowsChunk020
import QiushiCalibrationRowsChunk021
import QiushiCalibrationRowsChunk022
import QiushiCalibrationRowsChunk023
import QiushiCalibrationRowsChunk024
import QiushiCalibrationRowsChunk025
import QiushiCalibrationRowsChunk026
import QiushiCalibrationRowsChunk027
import QiushiCalibrationRowsChunk028
import QiushiCalibrationRowsChunk029
import QiushiCalibrationRowsChunk030
import QiushiCalibrationRowsChunk031
import QiushiCalibrationRowsChunk032
import QiushiCalibrationRowsChunk033
import QiushiCalibrationRowsChunk034
import QiushiCalibrationRowsChunk035
import QiushiCalibrationRowsChunk036
import QiushiCalibrationRowsChunk037
import QiushiCalibrationRowsChunk038
import QiushiCalibrationRowsChunk039
import QiushiCalibrationRowsChunk040
import QiushiCalibrationRowsChunk041
import QiushiCalibrationRowsChunk042
import QiushiCalibrationRowsChunk043
import QiushiCalibrationRowsChunk044
import QiushiCalibrationRowsChunk045
import QiushiCalibrationRowsChunk046
import QiushiCalibrationRowsChunk047
import QiushiCalibrationRowsChunk048
import QiushiCalibrationRowsChunk049
import QiushiCalibrationRowsChunk050
import QiushiCalibrationRowsChunk051
import QiushiCalibrationRowsChunk052
import QiushiCalibrationRowsChunk053
import QiushiCalibrationRowsChunk054
import QiushiCalibrationRowsChunk055
import QiushiCalibrationRowsChunk056
import QiushiCalibrationRowsChunk057

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem maskSorted000 : (data000.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead000 : (data000.map RowData.mask).head? = some 1 := by decide
theorem maskLast000 : (data000.map RowData.mask).getLast? = some 10179072500752 := by decide

theorem maskSorted001 : (data001.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead001 : (data001.map RowData.mask).head? = some 10995116277792 := by decide
theorem maskLast001 : (data001.map RowData.mask).getLast? = some 18014398509481984 := by decide

theorem maskSorted002 : (data002.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead002 : (data002.map RowData.mask).head? = some 18014400661159936 := by decide
theorem maskLast002 : (data002.map RowData.mask).getLast? = some 288802191458697472 := by decide

theorem maskSorted003 : (data003.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead003 : (data003.map RowData.mask).head? = some 288810953726755072 := by decide
theorem maskLast003 : (data003.map RowData.mask).getLast? = some 1300485452839657792 := by decide

theorem maskSorted004 : (data004.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead004 : (data004.map RowData.mask).head? = some 1302103242263511232 := by decide
theorem maskLast004 : (data004.map RowData.mask).getLast? = some 4657016761429532992 := by decide

theorem maskSorted005 : (data005.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead005 : (data005.map RowData.mask).head? = some 4657023332629225792 := by decide
theorem maskLast005 : (data005.map RowData.mask).getLast? = some 302821750714015999328512 := by decide

theorem maskSorted006 : (data006.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead006 : (data006.map RowData.mask).head? = some 303412046524374704980096 := by decide
theorem maskLast006 : (data006.map RowData.mask).getLast? = some 123792114981944880059645977 := by decide

theorem maskSorted007 : (data007.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead007 : (data007.map RowData.mask).head? = some 145071098353755500964741127 := by decide
theorem maskLast007 : (data007.map RowData.mask).getLast? = some 1856910169608534854631161857 := by decide

theorem maskSorted008 : (data008.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead008 : (data008.map RowData.mask).head? = some 1856910501649928182988537857 := by decide
theorem maskLast008 : (data008.map RowData.mask).getLast? = some 9903558093214905156354834432 := by decide

theorem maskSorted009 : (data009.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead009 : (data009.map RowData.mask).head? = some 9903595872146768113516675072 := by decide
theorem maskLast009 : (data009.map RowData.mask).getLast? = some 22286887550322687672098009092 := by decide

theorem maskSorted010 : (data010.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead010 : (data010.map RowData.mask).head? = some 22288360873325110779470432260 := by decide
theorem maskLast010 : (data010.map RowData.mask).getLast? = some 1267650619117695368159656148992 := by decide

theorem maskSorted011 : (data011.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead011 : (data011.map RowData.mask).head? = some 1267650638007161265553376542720 := by decide
theorem maskLast011 : (data011.map RowData.mask).getLast? = some 10101591322670429749244350955647 := by decide

theorem maskSorted012 : (data012.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead012 : (data012.map RowData.mask).head? = some 10101744858610739796456159314047 := by decide
theorem maskLast012 : (data012.map RowData.mask).getLast? = some 41832469807531570249391205793792 := by decide

theorem maskSorted013 : (data013.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead013 : (data013.map RowData.mask).head? = some 41832469811073345129144215683072 := by decide
theorem maskLast013 : (data013.map RowData.mask).getLast? = some 162259276830393955016693468102656 := by decide

theorem maskSorted014 : (data014.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead014 : (data014.map RowData.mask).head? = some 162259276831574546633047192633344 := by decide
theorem maskLast014 : (data014.map RowData.mask).getLast? = some 327053854877781874907394487616512 := by decide

theorem maskSorted015 : (data015.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead015 : (data015.map RowData.mask).head? = some 327053854897842709072027318223872 := by decide
theorem maskLast015 : (data015.map RowData.mask).getLast? = some 659178336297197122222749919477792 := by decide

theorem maskSorted016 : (data016.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead016 : (data016.map RowData.mask).head? = some 659178351408770768125540077404192 := by decide
theorem maskLast016 : (data016.map RowData.mask).getLast? = some 1299342179554648821805657767281152 := by decide

theorem maskSorted017 : (data017.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead017 : (data017.map RowData.mask).head? = some 1299342484808422305221190877184512 := by decide
theorem maskLast017 : (data017.map RowData.mask).getLast? = some 2068805810400086133290255454830617 := by decide

theorem maskSorted018 : (data018.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead018 : (data018.map RowData.mask).head? = some 2068805902882905821403443418365977 := by decide
theorem maskLast018 : (data018.map RowData.mask).getLast? = some 5197372412714787297713045490368512 := by decide

theorem maskSorted019 : (data019.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead019 : (data019.map RowData.mask).head? = some 5197377364458416084548079941844992 := by decide
theorem maskLast019 : (data019.map RowData.mask).getLast? = some 11033633300266596505358025812344832 := by decide

theorem maskSorted020 : (data020.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead020 : (data020.map RowData.mask).head? = some 11033635776146684300088746790879232 := by decide
theorem maskLast020 : (data020.map RowData.mask).getLast? = some 23365335863746739903300618667687940 := by decide

theorem maskSorted021 : (data021.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead021 : (data021.map RowData.mask).head? = some 23365335867033501787231133890510852 := by decide
theorem maskLast021 : (data021.map RowData.mask).getLast? = some 41619504511566709956290306470051840 := by decide

theorem maskSorted022 : (data022.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead022 : (data022.map RowData.mask).head? = some 41619504516383528344474293266022400 := by decide
theorem maskLast022 : (data022.map RowData.mask).getLast? = some 83076908270253532268375040612892672 := by decide

theorem maskSorted023 : (data023.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead023 : (data023.map RowData.mask).head? = some 83076908347927007094872100277583872 := by decide
theorem maskLast023 : (data023.map RowData.mask).getLast? = some 103845947228959371764346650372341792 := by decide

theorem maskSorted024 : (data024.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead024 : (data024.map RowData.mask).head? = some 103845957287222190958050388811448352 := by decide
theorem maskLast024 : (data024.map RowData.mask).getLast? = some 167451573690184933278190782530977792 := by decide

theorem maskSorted025 : (data025.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead025 : (data025.map RowData.mask).head? = some 167451573692593339607993583646277632 := by decide
theorem maskLast025 : (data025.map RowData.mask).getLast? = some 235326657426368506093847983800975442 := by decide

theorem maskSorted026 : (data026.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead026 : (data026.map RowData.mask).head? = some 235326657481159766453935128434442322 := by decide
theorem maskLast026 : (data026.map RowData.mask).getLast? = some 335146536312656707310203084449251392 := by decide

theorem maskSorted027 : (data027.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead027 : (data027.map RowData.mask).head? = some 335146536330719758026315631247228992 := by decide
theorem maskLast027 : (data027.map RowData.mask).getLast? = some 415485160737226887231406317649264642 := by decide

theorem maskSorted028 : (data028.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead028 : (data028.map RowData.mask).head? = some 415485160779173313099959328875479042 := by decide
theorem maskLast028 : (data028.map RowData.mask).getLast? = some 664776257178958565631621771515396096 := by decide

theorem maskSorted029 : (data029.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead029 : (data029.map RowData.mask).head? = some 664776257188629981447948434879807488 := by decide
theorem maskLast029 : (data029.map RowData.mask).getLast? = some 747690747629034660577102217814740992 := by decide

theorem maskSorted030 : (data030.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead030 : (data030.map RowData.mask).head? = some 747690747629052975961307896130572288 := by decide
theorem maskLast030 : (data030.map RowData.mask).getLast? = some 1329390256299836241298045148937060352 := by decide

theorem maskSorted031 : (data031.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead031 : (data031.map RowData.mask).head? = some 1329390257537629887204582863942975488 := by decide
theorem maskLast031 : (data031.map RowData.mask).getLast? = some 1412304746179128760830723658512074752 := by decide

theorem maskSorted032 : (data032.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead032 : (data032.map RowData.mask).head? = some 1412304746836784406701046736590211072 := by decide
theorem maskLast032 : (data032.map RowData.mask).getLast? = some 2658456070798617612447974181339922432 := by decide

theorem maskSorted033 : (data033.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead033 : (data033.map RowData.mask).head? = some 2658456070799212630624677218171748352 := by decide
theorem maskLast033 : (data033.map RowData.mask).getLast? = some 2670143730103936020889413724383740032 := by decide

theorem maskSorted034 : (data034.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead034 : (data034.map RowData.mask).head? = some 2670143730259358846351227291559788672 := by decide
theorem maskLast034 : (data034.map RowData.mask).getLast? = some 3323120696260023141905851062933422082 := by decide

theorem maskSorted035 : (data035.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead035 : (data035.map RowData.mask).head? = some 3323120697033747472376124607037603842 := by decide
theorem maskLast035 : (data035.map RowData.mask).getLast? = some 5316917053819454546454251507411845120 := by decide

theorem maskSorted036 : (data036.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead036 : (data036.map RowData.mask).head? = some 5316917053896807061629145387714478080 := by decide
theorem maskLast036 : (data036.map RowData.mask).getLast? = some 5358450358646254945400031604667072512 := by decide

theorem maskSorted037 : (data037.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead037 : (data037.map RowData.mask).head? = some 5358450359255553558485839890943590400 := by decide
theorem maskLast037 : (data037.map RowData.mask).getLast? = some 6231730143445337503046269734648557572 := by decide

theorem maskSorted038 : (data038.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead038 : (data038.map RowData.mask).head? = some 6231730143880437489083368086401200132 := by decide
theorem maskLast038 : (data038.map RowData.mask).getLast? = some 10633823966279364762162460176892821504 := by decide

theorem maskSorted039 : (data039.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead039 : (data039.map RowData.mask).head? = some 10633823966279402541094463871542886400 := by decide
theorem maskLast039 : (data039.map RowData.mask).getLast? = some 10644249768545031784761343217646968832 := by decide

theorem maskSorted040 : (data040.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead040 : (data040.map RowData.mask).head? = some 10644249778449159513579620317528072192 := by decide
theorem maskLast040 : (data040.map RowData.mask).getLast? = some 11298438637652430329266152050129895432 := by decide

theorem maskSorted041 : (data041.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead041 : (data041.map RowData.mask).head? = some 11298438637693694367603074542610677768 := by decide
theorem maskLast041 : (data041.map RowData.mask).getLast? = some 13396125895020162835675454891800674592 := by decide

theorem maskSorted042 : (data042.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead042 : (data042.map RowData.mask).head? = some 13396125898138883896214495407972040992 := by decide
theorem maskLast042 : (data042.map RowData.mask).getLast? = some 21267729062201904571605036430935457792 := by decide

theorem maskSorted043 : (data043.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead043 : (data043.map RowData.mask).head? = some 21267729062206740021204701052248522752 := by decide
theorem maskLast043 : (data043.map RowData.mask).getLast? = some 21309840416377010624995959133901684992 := by decide

theorem maskSorted044 : (data044.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead044 : (data044.map RowData.mask).head? = some 21309840417632176067584431746755854592 := by decide
theorem maskLast044 : (data044.map RowData.mask).getLast? = some 22596877275222332581858459115155619848 := by decide

theorem maskSorted045 : (data045.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead045 : (data045.map RowData.mask).head? = some 22596877275232648591445091621426692104 := by decide
theorem maskLast045 : (data045.map RowData.mask).getLast? = some 26688609472353709845019593877733056672 := by decide

theorem maskSorted046 : (data046.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead046 : (data046.map RowData.mask).head? = some 26688609475460601795647905292441690272 := by decide
theorem maskLast046 : (data046.map RowData.mask).getLast? = some 42535297133077393208442521669066555392 := by decide

theorem maskSorted047 : (data047.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead047 : (data047.map RowData.mask).head? = some 42535297133386878203852347689687580672 := by decide
theorem maskLast047 : (data047.map RowData.mask).getLast? = some 42556389615671702738013753848933650432 := by decide

theorem maskSorted048 : (data048.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead048 : (data048.map RowData.mask).head? = some 42556389620627618514250485038141673472 := by decide
theorem maskLast048 : (data048.map RowData.mask).getLast? = some 43304164033370353553726160662546355232 := by decide

theorem maskSorted049 : (data049.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead049 : (data049.map RowData.mask).head? = some 43304164043416480492917129004398679072 := by decide
theorem maskLast049 : (data049.map RowData.mask).getLast? = some 47852209160628156237222555207918944272 := by decide

theorem maskSorted050 : (data050.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead050 : (data050.map RowData.mask).head? = some 47852209166663113570432397610703650832 := by decide
theorem maskLast050 : (data050.map RowData.mask).getLast? = some 63802944155595376643536285791858720772 := by decide

theorem maskSorted051 : (data051.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead051 : (data051.map RowData.mask).head? = some 63802944169057973771465934228839989252 := by decide
theorem maskLast051 : (data051.map RowData.mask).getLast? = some 85070753989511445079207043435952603136 := by decide

theorem maskSorted052 : (data052.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead052 : (data052.map RowData.mask).head? = some 85070753989512049616480358166425763840 := by decide
theorem maskLast052 : (data052.map RowData.mask).getLast? = some 85113428832959842722333962393664652288 := by decide

theorem maskSorted053 : (data053.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead053 : (data053.map RowData.mask).head? = some 85153668479971173107900139799209574912 := by decide
theorem maskLast053 : (data053.map RowData.mask).getLast? = some 86399822301013547107542406476930744352 := by decide

theorem maskSorted054 : (data054.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead054 : (data054.map RowData.mask).head? = some 86399822304029663920207338897208770592 := by decide
theorem maskLast054 : (data054.map RowData.mask).getLast? = some 90476463056400970084132576742278767112 := by decide

theorem maskSorted055 : (data055.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead055 : (data055.map RowData.mask).head? = some 90477153310701182483226466040565768712 := by decide
theorem maskLast055 : (data055.map RowData.mask).getLast? = some 106365012666305530684272931682386257922 := by decide

theorem maskSorted056 : (data056.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead056 : (data056.map RowData.mask).head? = some 106365824135995048675402821052567562242 := by decide
theorem maskLast056 : (data056.map RowData.mask).getLast? = some 159548736241140407966290428776373811207 := by decide

theorem maskSorted057 : (data057.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead057 : (data057.map RowData.mask).head? = some 160130435117214084063880506793147762567 := by decide
theorem maskLast057 : (data057.map RowData.mask).getLast? = some 170141183420855150474555134921259614207 := by decide

def maskSuffix057 : List Nat := data057.map RowData.mask
theorem suffixSorted057 : maskSuffix057.IsChain (· < ·) := maskSorted057
theorem suffixHead057 : maskSuffix057.head? = some 160130435117214084063880506793147762567 := maskHead057

def maskSuffix056 : List Nat := data056.map RowData.mask ++ maskSuffix057
theorem suffixSorted056 : maskSuffix056.IsChain (· < ·) := by
  apply (maskSorted056).append suffixSorted057
  rw [maskLast056, suffixHead057]
  intro a ha b hb
  have hA : a = 159548736241140407966290428776373811207 := by simpa [eq_comm] using ha
  have hB : b = 160130435117214084063880506793147762567 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead056 : maskSuffix056.head? = some 106365824135995048675402821052567562242 := by
  change (data056.map RowData.mask ++ maskSuffix057).head? = _
  rw [List.head?_append, maskHead056]
  rfl

def maskSuffix055 : List Nat := data055.map RowData.mask ++ maskSuffix056
theorem suffixSorted055 : maskSuffix055.IsChain (· < ·) := by
  apply (maskSorted055).append suffixSorted056
  rw [maskLast055, suffixHead056]
  intro a ha b hb
  have hA : a = 106365012666305530684272931682386257922 := by simpa [eq_comm] using ha
  have hB : b = 106365824135995048675402821052567562242 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead055 : maskSuffix055.head? = some 90477153310701182483226466040565768712 := by
  change (data055.map RowData.mask ++ maskSuffix056).head? = _
  rw [List.head?_append, maskHead055]
  rfl

def maskSuffix054 : List Nat := data054.map RowData.mask ++ maskSuffix055
theorem suffixSorted054 : maskSuffix054.IsChain (· < ·) := by
  apply (maskSorted054).append suffixSorted055
  rw [maskLast054, suffixHead055]
  intro a ha b hb
  have hA : a = 90476463056400970084132576742278767112 := by simpa [eq_comm] using ha
  have hB : b = 90477153310701182483226466040565768712 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead054 : maskSuffix054.head? = some 86399822304029663920207338897208770592 := by
  change (data054.map RowData.mask ++ maskSuffix055).head? = _
  rw [List.head?_append, maskHead054]
  rfl

def maskSuffix053 : List Nat := data053.map RowData.mask ++ maskSuffix054
theorem suffixSorted053 : maskSuffix053.IsChain (· < ·) := by
  apply (maskSorted053).append suffixSorted054
  rw [maskLast053, suffixHead054]
  intro a ha b hb
  have hA : a = 86399822301013547107542406476930744352 := by simpa [eq_comm] using ha
  have hB : b = 86399822304029663920207338897208770592 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead053 : maskSuffix053.head? = some 85153668479971173107900139799209574912 := by
  change (data053.map RowData.mask ++ maskSuffix054).head? = _
  rw [List.head?_append, maskHead053]
  rfl

def maskSuffix052 : List Nat := data052.map RowData.mask ++ maskSuffix053
theorem suffixSorted052 : maskSuffix052.IsChain (· < ·) := by
  apply (maskSorted052).append suffixSorted053
  rw [maskLast052, suffixHead053]
  intro a ha b hb
  have hA : a = 85113428832959842722333962393664652288 := by simpa [eq_comm] using ha
  have hB : b = 85153668479971173107900139799209574912 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead052 : maskSuffix052.head? = some 85070753989512049616480358166425763840 := by
  change (data052.map RowData.mask ++ maskSuffix053).head? = _
  rw [List.head?_append, maskHead052]
  rfl

def maskSuffix051 : List Nat := data051.map RowData.mask ++ maskSuffix052
theorem suffixSorted051 : maskSuffix051.IsChain (· < ·) := by
  apply (maskSorted051).append suffixSorted052
  rw [maskLast051, suffixHead052]
  intro a ha b hb
  have hA : a = 85070753989511445079207043435952603136 := by simpa [eq_comm] using ha
  have hB : b = 85070753989512049616480358166425763840 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead051 : maskSuffix051.head? = some 63802944169057973771465934228839989252 := by
  change (data051.map RowData.mask ++ maskSuffix052).head? = _
  rw [List.head?_append, maskHead051]
  rfl

def maskSuffix050 : List Nat := data050.map RowData.mask ++ maskSuffix051
theorem suffixSorted050 : maskSuffix050.IsChain (· < ·) := by
  apply (maskSorted050).append suffixSorted051
  rw [maskLast050, suffixHead051]
  intro a ha b hb
  have hA : a = 63802944155595376643536285791858720772 := by simpa [eq_comm] using ha
  have hB : b = 63802944169057973771465934228839989252 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead050 : maskSuffix050.head? = some 47852209166663113570432397610703650832 := by
  change (data050.map RowData.mask ++ maskSuffix051).head? = _
  rw [List.head?_append, maskHead050]
  rfl

def maskSuffix049 : List Nat := data049.map RowData.mask ++ maskSuffix050
theorem suffixSorted049 : maskSuffix049.IsChain (· < ·) := by
  apply (maskSorted049).append suffixSorted050
  rw [maskLast049, suffixHead050]
  intro a ha b hb
  have hA : a = 47852209160628156237222555207918944272 := by simpa [eq_comm] using ha
  have hB : b = 47852209166663113570432397610703650832 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead049 : maskSuffix049.head? = some 43304164043416480492917129004398679072 := by
  change (data049.map RowData.mask ++ maskSuffix050).head? = _
  rw [List.head?_append, maskHead049]
  rfl

def maskSuffix048 : List Nat := data048.map RowData.mask ++ maskSuffix049
theorem suffixSorted048 : maskSuffix048.IsChain (· < ·) := by
  apply (maskSorted048).append suffixSorted049
  rw [maskLast048, suffixHead049]
  intro a ha b hb
  have hA : a = 43304164033370353553726160662546355232 := by simpa [eq_comm] using ha
  have hB : b = 43304164043416480492917129004398679072 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead048 : maskSuffix048.head? = some 42556389620627618514250485038141673472 := by
  change (data048.map RowData.mask ++ maskSuffix049).head? = _
  rw [List.head?_append, maskHead048]
  rfl

def maskSuffix047 : List Nat := data047.map RowData.mask ++ maskSuffix048
theorem suffixSorted047 : maskSuffix047.IsChain (· < ·) := by
  apply (maskSorted047).append suffixSorted048
  rw [maskLast047, suffixHead048]
  intro a ha b hb
  have hA : a = 42556389615671702738013753848933650432 := by simpa [eq_comm] using ha
  have hB : b = 42556389620627618514250485038141673472 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead047 : maskSuffix047.head? = some 42535297133386878203852347689687580672 := by
  change (data047.map RowData.mask ++ maskSuffix048).head? = _
  rw [List.head?_append, maskHead047]
  rfl

def maskSuffix046 : List Nat := data046.map RowData.mask ++ maskSuffix047
theorem suffixSorted046 : maskSuffix046.IsChain (· < ·) := by
  apply (maskSorted046).append suffixSorted047
  rw [maskLast046, suffixHead047]
  intro a ha b hb
  have hA : a = 42535297133077393208442521669066555392 := by simpa [eq_comm] using ha
  have hB : b = 42535297133386878203852347689687580672 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead046 : maskSuffix046.head? = some 26688609475460601795647905292441690272 := by
  change (data046.map RowData.mask ++ maskSuffix047).head? = _
  rw [List.head?_append, maskHead046]
  rfl

def maskSuffix045 : List Nat := data045.map RowData.mask ++ maskSuffix046
theorem suffixSorted045 : maskSuffix045.IsChain (· < ·) := by
  apply (maskSorted045).append suffixSorted046
  rw [maskLast045, suffixHead046]
  intro a ha b hb
  have hA : a = 26688609472353709845019593877733056672 := by simpa [eq_comm] using ha
  have hB : b = 26688609475460601795647905292441690272 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead045 : maskSuffix045.head? = some 22596877275232648591445091621426692104 := by
  change (data045.map RowData.mask ++ maskSuffix046).head? = _
  rw [List.head?_append, maskHead045]
  rfl

def maskSuffix044 : List Nat := data044.map RowData.mask ++ maskSuffix045
theorem suffixSorted044 : maskSuffix044.IsChain (· < ·) := by
  apply (maskSorted044).append suffixSorted045
  rw [maskLast044, suffixHead045]
  intro a ha b hb
  have hA : a = 22596877275222332581858459115155619848 := by simpa [eq_comm] using ha
  have hB : b = 22596877275232648591445091621426692104 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead044 : maskSuffix044.head? = some 21309840417632176067584431746755854592 := by
  change (data044.map RowData.mask ++ maskSuffix045).head? = _
  rw [List.head?_append, maskHead044]
  rfl

def maskSuffix043 : List Nat := data043.map RowData.mask ++ maskSuffix044
theorem suffixSorted043 : maskSuffix043.IsChain (· < ·) := by
  apply (maskSorted043).append suffixSorted044
  rw [maskLast043, suffixHead044]
  intro a ha b hb
  have hA : a = 21309840416377010624995959133901684992 := by simpa [eq_comm] using ha
  have hB : b = 21309840417632176067584431746755854592 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead043 : maskSuffix043.head? = some 21267729062206740021204701052248522752 := by
  change (data043.map RowData.mask ++ maskSuffix044).head? = _
  rw [List.head?_append, maskHead043]
  rfl

def maskSuffix042 : List Nat := data042.map RowData.mask ++ maskSuffix043
theorem suffixSorted042 : maskSuffix042.IsChain (· < ·) := by
  apply (maskSorted042).append suffixSorted043
  rw [maskLast042, suffixHead043]
  intro a ha b hb
  have hA : a = 21267729062201904571605036430935457792 := by simpa [eq_comm] using ha
  have hB : b = 21267729062206740021204701052248522752 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead042 : maskSuffix042.head? = some 13396125898138883896214495407972040992 := by
  change (data042.map RowData.mask ++ maskSuffix043).head? = _
  rw [List.head?_append, maskHead042]
  rfl

def maskSuffix041 : List Nat := data041.map RowData.mask ++ maskSuffix042
theorem suffixSorted041 : maskSuffix041.IsChain (· < ·) := by
  apply (maskSorted041).append suffixSorted042
  rw [maskLast041, suffixHead042]
  intro a ha b hb
  have hA : a = 13396125895020162835675454891800674592 := by simpa [eq_comm] using ha
  have hB : b = 13396125898138883896214495407972040992 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead041 : maskSuffix041.head? = some 11298438637693694367603074542610677768 := by
  change (data041.map RowData.mask ++ maskSuffix042).head? = _
  rw [List.head?_append, maskHead041]
  rfl

def maskSuffix040 : List Nat := data040.map RowData.mask ++ maskSuffix041
theorem suffixSorted040 : maskSuffix040.IsChain (· < ·) := by
  apply (maskSorted040).append suffixSorted041
  rw [maskLast040, suffixHead041]
  intro a ha b hb
  have hA : a = 11298438637652430329266152050129895432 := by simpa [eq_comm] using ha
  have hB : b = 11298438637693694367603074542610677768 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead040 : maskSuffix040.head? = some 10644249778449159513579620317528072192 := by
  change (data040.map RowData.mask ++ maskSuffix041).head? = _
  rw [List.head?_append, maskHead040]
  rfl

def maskSuffix039 : List Nat := data039.map RowData.mask ++ maskSuffix040
theorem suffixSorted039 : maskSuffix039.IsChain (· < ·) := by
  apply (maskSorted039).append suffixSorted040
  rw [maskLast039, suffixHead040]
  intro a ha b hb
  have hA : a = 10644249768545031784761343217646968832 := by simpa [eq_comm] using ha
  have hB : b = 10644249778449159513579620317528072192 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead039 : maskSuffix039.head? = some 10633823966279402541094463871542886400 := by
  change (data039.map RowData.mask ++ maskSuffix040).head? = _
  rw [List.head?_append, maskHead039]
  rfl

def maskSuffix038 : List Nat := data038.map RowData.mask ++ maskSuffix039
theorem suffixSorted038 : maskSuffix038.IsChain (· < ·) := by
  apply (maskSorted038).append suffixSorted039
  rw [maskLast038, suffixHead039]
  intro a ha b hb
  have hA : a = 10633823966279364762162460176892821504 := by simpa [eq_comm] using ha
  have hB : b = 10633823966279402541094463871542886400 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead038 : maskSuffix038.head? = some 6231730143880437489083368086401200132 := by
  change (data038.map RowData.mask ++ maskSuffix039).head? = _
  rw [List.head?_append, maskHead038]
  rfl

def maskSuffix037 : List Nat := data037.map RowData.mask ++ maskSuffix038
theorem suffixSorted037 : maskSuffix037.IsChain (· < ·) := by
  apply (maskSorted037).append suffixSorted038
  rw [maskLast037, suffixHead038]
  intro a ha b hb
  have hA : a = 6231730143445337503046269734648557572 := by simpa [eq_comm] using ha
  have hB : b = 6231730143880437489083368086401200132 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead037 : maskSuffix037.head? = some 5358450359255553558485839890943590400 := by
  change (data037.map RowData.mask ++ maskSuffix038).head? = _
  rw [List.head?_append, maskHead037]
  rfl

def maskSuffix036 : List Nat := data036.map RowData.mask ++ maskSuffix037
theorem suffixSorted036 : maskSuffix036.IsChain (· < ·) := by
  apply (maskSorted036).append suffixSorted037
  rw [maskLast036, suffixHead037]
  intro a ha b hb
  have hA : a = 5358450358646254945400031604667072512 := by simpa [eq_comm] using ha
  have hB : b = 5358450359255553558485839890943590400 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead036 : maskSuffix036.head? = some 5316917053896807061629145387714478080 := by
  change (data036.map RowData.mask ++ maskSuffix037).head? = _
  rw [List.head?_append, maskHead036]
  rfl

def maskSuffix035 : List Nat := data035.map RowData.mask ++ maskSuffix036
theorem suffixSorted035 : maskSuffix035.IsChain (· < ·) := by
  apply (maskSorted035).append suffixSorted036
  rw [maskLast035, suffixHead036]
  intro a ha b hb
  have hA : a = 5316917053819454546454251507411845120 := by simpa [eq_comm] using ha
  have hB : b = 5316917053896807061629145387714478080 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead035 : maskSuffix035.head? = some 3323120697033747472376124607037603842 := by
  change (data035.map RowData.mask ++ maskSuffix036).head? = _
  rw [List.head?_append, maskHead035]
  rfl

def maskSuffix034 : List Nat := data034.map RowData.mask ++ maskSuffix035
theorem suffixSorted034 : maskSuffix034.IsChain (· < ·) := by
  apply (maskSorted034).append suffixSorted035
  rw [maskLast034, suffixHead035]
  intro a ha b hb
  have hA : a = 3323120696260023141905851062933422082 := by simpa [eq_comm] using ha
  have hB : b = 3323120697033747472376124607037603842 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead034 : maskSuffix034.head? = some 2670143730259358846351227291559788672 := by
  change (data034.map RowData.mask ++ maskSuffix035).head? = _
  rw [List.head?_append, maskHead034]
  rfl

def maskSuffix033 : List Nat := data033.map RowData.mask ++ maskSuffix034
theorem suffixSorted033 : maskSuffix033.IsChain (· < ·) := by
  apply (maskSorted033).append suffixSorted034
  rw [maskLast033, suffixHead034]
  intro a ha b hb
  have hA : a = 2670143730103936020889413724383740032 := by simpa [eq_comm] using ha
  have hB : b = 2670143730259358846351227291559788672 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead033 : maskSuffix033.head? = some 2658456070799212630624677218171748352 := by
  change (data033.map RowData.mask ++ maskSuffix034).head? = _
  rw [List.head?_append, maskHead033]
  rfl

def maskSuffix032 : List Nat := data032.map RowData.mask ++ maskSuffix033
theorem suffixSorted032 : maskSuffix032.IsChain (· < ·) := by
  apply (maskSorted032).append suffixSorted033
  rw [maskLast032, suffixHead033]
  intro a ha b hb
  have hA : a = 2658456070798617612447974181339922432 := by simpa [eq_comm] using ha
  have hB : b = 2658456070799212630624677218171748352 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead032 : maskSuffix032.head? = some 1412304746836784406701046736590211072 := by
  change (data032.map RowData.mask ++ maskSuffix033).head? = _
  rw [List.head?_append, maskHead032]
  rfl

def maskSuffix031 : List Nat := data031.map RowData.mask ++ maskSuffix032
theorem suffixSorted031 : maskSuffix031.IsChain (· < ·) := by
  apply (maskSorted031).append suffixSorted032
  rw [maskLast031, suffixHead032]
  intro a ha b hb
  have hA : a = 1412304746179128760830723658512074752 := by simpa [eq_comm] using ha
  have hB : b = 1412304746836784406701046736590211072 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead031 : maskSuffix031.head? = some 1329390257537629887204582863942975488 := by
  change (data031.map RowData.mask ++ maskSuffix032).head? = _
  rw [List.head?_append, maskHead031]
  rfl

def maskSuffix030 : List Nat := data030.map RowData.mask ++ maskSuffix031
theorem suffixSorted030 : maskSuffix030.IsChain (· < ·) := by
  apply (maskSorted030).append suffixSorted031
  rw [maskLast030, suffixHead031]
  intro a ha b hb
  have hA : a = 1329390256299836241298045148937060352 := by simpa [eq_comm] using ha
  have hB : b = 1329390257537629887204582863942975488 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead030 : maskSuffix030.head? = some 747690747629052975961307896130572288 := by
  change (data030.map RowData.mask ++ maskSuffix031).head? = _
  rw [List.head?_append, maskHead030]
  rfl

def maskSuffix029 : List Nat := data029.map RowData.mask ++ maskSuffix030
theorem suffixSorted029 : maskSuffix029.IsChain (· < ·) := by
  apply (maskSorted029).append suffixSorted030
  rw [maskLast029, suffixHead030]
  intro a ha b hb
  have hA : a = 747690747629034660577102217814740992 := by simpa [eq_comm] using ha
  have hB : b = 747690747629052975961307896130572288 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead029 : maskSuffix029.head? = some 664776257188629981447948434879807488 := by
  change (data029.map RowData.mask ++ maskSuffix030).head? = _
  rw [List.head?_append, maskHead029]
  rfl

def maskSuffix028 : List Nat := data028.map RowData.mask ++ maskSuffix029
theorem suffixSorted028 : maskSuffix028.IsChain (· < ·) := by
  apply (maskSorted028).append suffixSorted029
  rw [maskLast028, suffixHead029]
  intro a ha b hb
  have hA : a = 664776257178958565631621771515396096 := by simpa [eq_comm] using ha
  have hB : b = 664776257188629981447948434879807488 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead028 : maskSuffix028.head? = some 415485160779173313099959328875479042 := by
  change (data028.map RowData.mask ++ maskSuffix029).head? = _
  rw [List.head?_append, maskHead028]
  rfl

def maskSuffix027 : List Nat := data027.map RowData.mask ++ maskSuffix028
theorem suffixSorted027 : maskSuffix027.IsChain (· < ·) := by
  apply (maskSorted027).append suffixSorted028
  rw [maskLast027, suffixHead028]
  intro a ha b hb
  have hA : a = 415485160737226887231406317649264642 := by simpa [eq_comm] using ha
  have hB : b = 415485160779173313099959328875479042 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead027 : maskSuffix027.head? = some 335146536330719758026315631247228992 := by
  change (data027.map RowData.mask ++ maskSuffix028).head? = _
  rw [List.head?_append, maskHead027]
  rfl

def maskSuffix026 : List Nat := data026.map RowData.mask ++ maskSuffix027
theorem suffixSorted026 : maskSuffix026.IsChain (· < ·) := by
  apply (maskSorted026).append suffixSorted027
  rw [maskLast026, suffixHead027]
  intro a ha b hb
  have hA : a = 335146536312656707310203084449251392 := by simpa [eq_comm] using ha
  have hB : b = 335146536330719758026315631247228992 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead026 : maskSuffix026.head? = some 235326657481159766453935128434442322 := by
  change (data026.map RowData.mask ++ maskSuffix027).head? = _
  rw [List.head?_append, maskHead026]
  rfl

def maskSuffix025 : List Nat := data025.map RowData.mask ++ maskSuffix026
theorem suffixSorted025 : maskSuffix025.IsChain (· < ·) := by
  apply (maskSorted025).append suffixSorted026
  rw [maskLast025, suffixHead026]
  intro a ha b hb
  have hA : a = 235326657426368506093847983800975442 := by simpa [eq_comm] using ha
  have hB : b = 235326657481159766453935128434442322 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead025 : maskSuffix025.head? = some 167451573692593339607993583646277632 := by
  change (data025.map RowData.mask ++ maskSuffix026).head? = _
  rw [List.head?_append, maskHead025]
  rfl

def maskSuffix024 : List Nat := data024.map RowData.mask ++ maskSuffix025
theorem suffixSorted024 : maskSuffix024.IsChain (· < ·) := by
  apply (maskSorted024).append suffixSorted025
  rw [maskLast024, suffixHead025]
  intro a ha b hb
  have hA : a = 167451573690184933278190782530977792 := by simpa [eq_comm] using ha
  have hB : b = 167451573692593339607993583646277632 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead024 : maskSuffix024.head? = some 103845957287222190958050388811448352 := by
  change (data024.map RowData.mask ++ maskSuffix025).head? = _
  rw [List.head?_append, maskHead024]
  rfl

def maskSuffix023 : List Nat := data023.map RowData.mask ++ maskSuffix024
theorem suffixSorted023 : maskSuffix023.IsChain (· < ·) := by
  apply (maskSorted023).append suffixSorted024
  rw [maskLast023, suffixHead024]
  intro a ha b hb
  have hA : a = 103845947228959371764346650372341792 := by simpa [eq_comm] using ha
  have hB : b = 103845957287222190958050388811448352 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead023 : maskSuffix023.head? = some 83076908347927007094872100277583872 := by
  change (data023.map RowData.mask ++ maskSuffix024).head? = _
  rw [List.head?_append, maskHead023]
  rfl

def maskSuffix022 : List Nat := data022.map RowData.mask ++ maskSuffix023
theorem suffixSorted022 : maskSuffix022.IsChain (· < ·) := by
  apply (maskSorted022).append suffixSorted023
  rw [maskLast022, suffixHead023]
  intro a ha b hb
  have hA : a = 83076908270253532268375040612892672 := by simpa [eq_comm] using ha
  have hB : b = 83076908347927007094872100277583872 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead022 : maskSuffix022.head? = some 41619504516383528344474293266022400 := by
  change (data022.map RowData.mask ++ maskSuffix023).head? = _
  rw [List.head?_append, maskHead022]
  rfl

def maskSuffix021 : List Nat := data021.map RowData.mask ++ maskSuffix022
theorem suffixSorted021 : maskSuffix021.IsChain (· < ·) := by
  apply (maskSorted021).append suffixSorted022
  rw [maskLast021, suffixHead022]
  intro a ha b hb
  have hA : a = 41619504511566709956290306470051840 := by simpa [eq_comm] using ha
  have hB : b = 41619504516383528344474293266022400 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead021 : maskSuffix021.head? = some 23365335867033501787231133890510852 := by
  change (data021.map RowData.mask ++ maskSuffix022).head? = _
  rw [List.head?_append, maskHead021]
  rfl

def maskSuffix020 : List Nat := data020.map RowData.mask ++ maskSuffix021
theorem suffixSorted020 : maskSuffix020.IsChain (· < ·) := by
  apply (maskSorted020).append suffixSorted021
  rw [maskLast020, suffixHead021]
  intro a ha b hb
  have hA : a = 23365335863746739903300618667687940 := by simpa [eq_comm] using ha
  have hB : b = 23365335867033501787231133890510852 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead020 : maskSuffix020.head? = some 11033635776146684300088746790879232 := by
  change (data020.map RowData.mask ++ maskSuffix021).head? = _
  rw [List.head?_append, maskHead020]
  rfl

def maskSuffix019 : List Nat := data019.map RowData.mask ++ maskSuffix020
theorem suffixSorted019 : maskSuffix019.IsChain (· < ·) := by
  apply (maskSorted019).append suffixSorted020
  rw [maskLast019, suffixHead020]
  intro a ha b hb
  have hA : a = 11033633300266596505358025812344832 := by simpa [eq_comm] using ha
  have hB : b = 11033635776146684300088746790879232 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead019 : maskSuffix019.head? = some 5197377364458416084548079941844992 := by
  change (data019.map RowData.mask ++ maskSuffix020).head? = _
  rw [List.head?_append, maskHead019]
  rfl

def maskSuffix018 : List Nat := data018.map RowData.mask ++ maskSuffix019
theorem suffixSorted018 : maskSuffix018.IsChain (· < ·) := by
  apply (maskSorted018).append suffixSorted019
  rw [maskLast018, suffixHead019]
  intro a ha b hb
  have hA : a = 5197372412714787297713045490368512 := by simpa [eq_comm] using ha
  have hB : b = 5197377364458416084548079941844992 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead018 : maskSuffix018.head? = some 2068805902882905821403443418365977 := by
  change (data018.map RowData.mask ++ maskSuffix019).head? = _
  rw [List.head?_append, maskHead018]
  rfl

def maskSuffix017 : List Nat := data017.map RowData.mask ++ maskSuffix018
theorem suffixSorted017 : maskSuffix017.IsChain (· < ·) := by
  apply (maskSorted017).append suffixSorted018
  rw [maskLast017, suffixHead018]
  intro a ha b hb
  have hA : a = 2068805810400086133290255454830617 := by simpa [eq_comm] using ha
  have hB : b = 2068805902882905821403443418365977 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead017 : maskSuffix017.head? = some 1299342484808422305221190877184512 := by
  change (data017.map RowData.mask ++ maskSuffix018).head? = _
  rw [List.head?_append, maskHead017]
  rfl

def maskSuffix016 : List Nat := data016.map RowData.mask ++ maskSuffix017
theorem suffixSorted016 : maskSuffix016.IsChain (· < ·) := by
  apply (maskSorted016).append suffixSorted017
  rw [maskLast016, suffixHead017]
  intro a ha b hb
  have hA : a = 1299342179554648821805657767281152 := by simpa [eq_comm] using ha
  have hB : b = 1299342484808422305221190877184512 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead016 : maskSuffix016.head? = some 659178351408770768125540077404192 := by
  change (data016.map RowData.mask ++ maskSuffix017).head? = _
  rw [List.head?_append, maskHead016]
  rfl

def maskSuffix015 : List Nat := data015.map RowData.mask ++ maskSuffix016
theorem suffixSorted015 : maskSuffix015.IsChain (· < ·) := by
  apply (maskSorted015).append suffixSorted016
  rw [maskLast015, suffixHead016]
  intro a ha b hb
  have hA : a = 659178336297197122222749919477792 := by simpa [eq_comm] using ha
  have hB : b = 659178351408770768125540077404192 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead015 : maskSuffix015.head? = some 327053854897842709072027318223872 := by
  change (data015.map RowData.mask ++ maskSuffix016).head? = _
  rw [List.head?_append, maskHead015]
  rfl

def maskSuffix014 : List Nat := data014.map RowData.mask ++ maskSuffix015
theorem suffixSorted014 : maskSuffix014.IsChain (· < ·) := by
  apply (maskSorted014).append suffixSorted015
  rw [maskLast014, suffixHead015]
  intro a ha b hb
  have hA : a = 327053854877781874907394487616512 := by simpa [eq_comm] using ha
  have hB : b = 327053854897842709072027318223872 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead014 : maskSuffix014.head? = some 162259276831574546633047192633344 := by
  change (data014.map RowData.mask ++ maskSuffix015).head? = _
  rw [List.head?_append, maskHead014]
  rfl

def maskSuffix013 : List Nat := data013.map RowData.mask ++ maskSuffix014
theorem suffixSorted013 : maskSuffix013.IsChain (· < ·) := by
  apply (maskSorted013).append suffixSorted014
  rw [maskLast013, suffixHead014]
  intro a ha b hb
  have hA : a = 162259276830393955016693468102656 := by simpa [eq_comm] using ha
  have hB : b = 162259276831574546633047192633344 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead013 : maskSuffix013.head? = some 41832469811073345129144215683072 := by
  change (data013.map RowData.mask ++ maskSuffix014).head? = _
  rw [List.head?_append, maskHead013]
  rfl

def maskSuffix012 : List Nat := data012.map RowData.mask ++ maskSuffix013
theorem suffixSorted012 : maskSuffix012.IsChain (· < ·) := by
  apply (maskSorted012).append suffixSorted013
  rw [maskLast012, suffixHead013]
  intro a ha b hb
  have hA : a = 41832469807531570249391205793792 := by simpa [eq_comm] using ha
  have hB : b = 41832469811073345129144215683072 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead012 : maskSuffix012.head? = some 10101744858610739796456159314047 := by
  change (data012.map RowData.mask ++ maskSuffix013).head? = _
  rw [List.head?_append, maskHead012]
  rfl

def maskSuffix011 : List Nat := data011.map RowData.mask ++ maskSuffix012
theorem suffixSorted011 : maskSuffix011.IsChain (· < ·) := by
  apply (maskSorted011).append suffixSorted012
  rw [maskLast011, suffixHead012]
  intro a ha b hb
  have hA : a = 10101591322670429749244350955647 := by simpa [eq_comm] using ha
  have hB : b = 10101744858610739796456159314047 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead011 : maskSuffix011.head? = some 1267650638007161265553376542720 := by
  change (data011.map RowData.mask ++ maskSuffix012).head? = _
  rw [List.head?_append, maskHead011]
  rfl

def maskSuffix010 : List Nat := data010.map RowData.mask ++ maskSuffix011
theorem suffixSorted010 : maskSuffix010.IsChain (· < ·) := by
  apply (maskSorted010).append suffixSorted011
  rw [maskLast010, suffixHead011]
  intro a ha b hb
  have hA : a = 1267650619117695368159656148992 := by simpa [eq_comm] using ha
  have hB : b = 1267650638007161265553376542720 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead010 : maskSuffix010.head? = some 22288360873325110779470432260 := by
  change (data010.map RowData.mask ++ maskSuffix011).head? = _
  rw [List.head?_append, maskHead010]
  rfl

def maskSuffix009 : List Nat := data009.map RowData.mask ++ maskSuffix010
theorem suffixSorted009 : maskSuffix009.IsChain (· < ·) := by
  apply (maskSorted009).append suffixSorted010
  rw [maskLast009, suffixHead010]
  intro a ha b hb
  have hA : a = 22286887550322687672098009092 := by simpa [eq_comm] using ha
  have hB : b = 22288360873325110779470432260 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead009 : maskSuffix009.head? = some 9903595872146768113516675072 := by
  change (data009.map RowData.mask ++ maskSuffix010).head? = _
  rw [List.head?_append, maskHead009]
  rfl

def maskSuffix008 : List Nat := data008.map RowData.mask ++ maskSuffix009
theorem suffixSorted008 : maskSuffix008.IsChain (· < ·) := by
  apply (maskSorted008).append suffixSorted009
  rw [maskLast008, suffixHead009]
  intro a ha b hb
  have hA : a = 9903558093214905156354834432 := by simpa [eq_comm] using ha
  have hB : b = 9903595872146768113516675072 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead008 : maskSuffix008.head? = some 1856910501649928182988537857 := by
  change (data008.map RowData.mask ++ maskSuffix009).head? = _
  rw [List.head?_append, maskHead008]
  rfl

def maskSuffix007 : List Nat := data007.map RowData.mask ++ maskSuffix008
theorem suffixSorted007 : maskSuffix007.IsChain (· < ·) := by
  apply (maskSorted007).append suffixSorted008
  rw [maskLast007, suffixHead008]
  intro a ha b hb
  have hA : a = 1856910169608534854631161857 := by simpa [eq_comm] using ha
  have hB : b = 1856910501649928182988537857 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead007 : maskSuffix007.head? = some 145071098353755500964741127 := by
  change (data007.map RowData.mask ++ maskSuffix008).head? = _
  rw [List.head?_append, maskHead007]
  rfl

def maskSuffix006 : List Nat := data006.map RowData.mask ++ maskSuffix007
theorem suffixSorted006 : maskSuffix006.IsChain (· < ·) := by
  apply (maskSorted006).append suffixSorted007
  rw [maskLast006, suffixHead007]
  intro a ha b hb
  have hA : a = 123792114981944880059645977 := by simpa [eq_comm] using ha
  have hB : b = 145071098353755500964741127 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead006 : maskSuffix006.head? = some 303412046524374704980096 := by
  change (data006.map RowData.mask ++ maskSuffix007).head? = _
  rw [List.head?_append, maskHead006]
  rfl

def maskSuffix005 : List Nat := data005.map RowData.mask ++ maskSuffix006
theorem suffixSorted005 : maskSuffix005.IsChain (· < ·) := by
  apply (maskSorted005).append suffixSorted006
  rw [maskLast005, suffixHead006]
  intro a ha b hb
  have hA : a = 302821750714015999328512 := by simpa [eq_comm] using ha
  have hB : b = 303412046524374704980096 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead005 : maskSuffix005.head? = some 4657023332629225792 := by
  change (data005.map RowData.mask ++ maskSuffix006).head? = _
  rw [List.head?_append, maskHead005]
  rfl

def maskSuffix004 : List Nat := data004.map RowData.mask ++ maskSuffix005
theorem suffixSorted004 : maskSuffix004.IsChain (· < ·) := by
  apply (maskSorted004).append suffixSorted005
  rw [maskLast004, suffixHead005]
  intro a ha b hb
  have hA : a = 4657016761429532992 := by simpa [eq_comm] using ha
  have hB : b = 4657023332629225792 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead004 : maskSuffix004.head? = some 1302103242263511232 := by
  change (data004.map RowData.mask ++ maskSuffix005).head? = _
  rw [List.head?_append, maskHead004]
  rfl

def maskSuffix003 : List Nat := data003.map RowData.mask ++ maskSuffix004
theorem suffixSorted003 : maskSuffix003.IsChain (· < ·) := by
  apply (maskSorted003).append suffixSorted004
  rw [maskLast003, suffixHead004]
  intro a ha b hb
  have hA : a = 1300485452839657792 := by simpa [eq_comm] using ha
  have hB : b = 1302103242263511232 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead003 : maskSuffix003.head? = some 288810953726755072 := by
  change (data003.map RowData.mask ++ maskSuffix004).head? = _
  rw [List.head?_append, maskHead003]
  rfl

def maskSuffix002 : List Nat := data002.map RowData.mask ++ maskSuffix003
theorem suffixSorted002 : maskSuffix002.IsChain (· < ·) := by
  apply (maskSorted002).append suffixSorted003
  rw [maskLast002, suffixHead003]
  intro a ha b hb
  have hA : a = 288802191458697472 := by simpa [eq_comm] using ha
  have hB : b = 288810953726755072 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead002 : maskSuffix002.head? = some 18014400661159936 := by
  change (data002.map RowData.mask ++ maskSuffix003).head? = _
  rw [List.head?_append, maskHead002]
  rfl

def maskSuffix001 : List Nat := data001.map RowData.mask ++ maskSuffix002
theorem suffixSorted001 : maskSuffix001.IsChain (· < ·) := by
  apply (maskSorted001).append suffixSorted002
  rw [maskLast001, suffixHead002]
  intro a ha b hb
  have hA : a = 18014398509481984 := by simpa [eq_comm] using ha
  have hB : b = 18014400661159936 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead001 : maskSuffix001.head? = some 10995116277792 := by
  change (data001.map RowData.mask ++ maskSuffix002).head? = _
  rw [List.head?_append, maskHead001]
  rfl

def maskSuffix000 : List Nat := data000.map RowData.mask ++ maskSuffix001
theorem suffixSorted000 : maskSuffix000.IsChain (· < ·) := by
  apply (maskSorted000).append suffixSorted001
  rw [maskLast000, suffixHead001]
  intro a ha b hb
  have hA : a = 10179072500752 := by simpa [eq_comm] using ha
  have hB : b = 10995116277792 := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead000 : maskSuffix000.head? = some 1 := by
  change (data000.map RowData.mask ++ maskSuffix001).head? = _
  rw [List.head?_append, maskHead000]
  rfl

end QiushiMatmul.CalibrationRows
