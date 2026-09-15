import QiushiLineCoverageDefs
import QiushiLineCoverageChunk00
import QiushiLineCoverageChunk01
import QiushiLineCoverageChunk02
import QiushiLineCoverageChunk03
import QiushiLineCoverageChunk04
import QiushiLineCoverageChunk05
import QiushiLineCoverageChunk06
import QiushiLineCoverageChunk07

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
namespace QiushiMatmul

theorem lineSource_all (i : Fin 255)
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane i) (lineSourceLb i) := by
  fin_cases i
  · exact lineSrc0_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc1_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc2_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc3_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc4_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc5_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc6_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc7_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc8_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc9_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc10_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc11_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc12_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc13_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc14_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc15_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc16_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc17_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc18_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc19_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc20_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc21_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc22_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc23_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc24_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc25_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc26_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc27_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc28_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc29_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc30_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc31_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc32_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc33_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc34_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc35_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc36_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc37_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc38_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc39_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc40_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc41_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc42_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc43_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc44_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc45_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc46_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc47_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc48_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc49_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc50_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc51_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc52_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc53_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc54_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc55_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc56_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc57_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc58_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc59_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc60_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc61_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc62_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc63_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc64_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc65_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc66_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc67_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc68_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc69_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc70_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc71_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc72_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc73_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc74_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc75_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc76_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc77_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc78_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc79_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc80_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc81_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc82_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc83_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc84_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc85_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc86_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc87_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc88_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc89_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc90_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc91_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc92_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc93_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc94_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc95_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc96_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc97_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc98_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc99_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc100_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc101_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc102_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc103_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc104_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc105_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc106_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc107_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc108_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc109_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc110_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc111_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc112_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc113_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc114_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc115_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc116_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc117_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc118_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc119_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc120_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc121_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc122_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc123_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc124_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc125_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc126_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc127_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc128_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc129_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc130_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc131_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc132_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc133_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc134_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc135_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc136_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc137_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc138_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc139_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc140_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc141_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc142_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc143_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc144_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc145_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc146_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc147_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc148_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc149_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc150_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc151_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc152_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc153_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc154_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc155_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc156_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc157_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc158_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc159_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc160_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc161_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc162_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc163_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc164_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc165_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc166_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc167_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc168_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc169_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc170_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc171_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc172_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc173_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc174_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc175_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc176_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc177_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc178_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc179_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc180_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc181_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc182_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc183_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc184_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc185_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc186_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc187_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc188_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc189_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc190_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc191_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc192_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc193_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc194_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc195_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc196_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc197_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc198_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc199_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc200_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc201_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc202_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc203_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc204_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc205_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc206_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc207_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc208_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc209_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc210_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc211_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc212_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc213_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc214_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc215_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc216_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc217_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc218_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc219_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc220_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc221_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc222_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc223_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc224_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc225_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc226_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc227_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc228_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc229_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc230_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc231_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc232_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc233_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc234_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc235_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc236_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc237_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc238_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc239_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc240_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc241_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc242_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc243_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc244_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc245_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc246_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc247_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc248_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc249_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc250_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc251_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc252_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc253_bound h478 h479 h480 h481 h482 h483
  · exact lineSrc254_bound h478 h479 h480 h481 h482 h483

theorem lineRank1_lb19_conditional
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast lineRank1 19 := by
  apply quotientRankAtLeast_of_occupation_noModel lineRank1 18
  intro r hr D
  exact direct_coverage_quotient_decomp_false_of_boolEq_cover
    lineSourcePlane lineSourceLb
    (fun _ => 1) 1 18
    lineCoverB
    lineRank1_le_source
    (fun i => lineSource_all i line478_ledger line479_ledger h480 h481 h482 h483)
    (by decide)
    lineCoverSound
    lineMatCoverage
    hr
    (by decide)
    D

#print axioms lineRank1_lb19_conditional
end QiushiMatmul
