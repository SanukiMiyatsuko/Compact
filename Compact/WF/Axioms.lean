import Compact.WF.F0WF
import Compact.WF.FXWF
import Compact.WF.FYWF
import Compact.WF.FYL6
import Compact.WF.FZL6
import Compact.WF.FWL6

/-! 構成的な整列性証明で使う定義・定理が `Classical.choice` に依存しないことの検査。
`#guard_msgs` で `#print axioms` の出力を固定するので、依存が増えるとビルドが失敗する。 -/

/-- info: 'RTKA.cmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.cmp

/-- info: 'RTKA.inC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.inC

/-- info: 'RTKA.isNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.isNF

/-- info: 'RTKA.cmp_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.cmp_self

/-- info: 'RTKA.cmp_swap_F0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.cmp_swap_F0

/-- info: 'RTKA.eq_of_cmp_eq_F0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.eq_of_cmp_eq_F0

/-- info: 'RTKA.lt_trans_F0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.lt_trans_F0

/-- info: 'RTKA.D_W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.D_W

/-- info: 'RTKA.one_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.one_step

/-- info: 'RTKA.W_psi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.W_psi

/-- info: 'RTKA.wellFounded_F0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.wellFounded_F0

/-- info: 'RTKA.cmp_swap_FX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.cmp_swap_FX

/-- info: 'RTKA.eq_of_cmp_eq_FX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.eq_of_cmp_eq_FX

/-- info: 'RTKA.lt_trans_FX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.lt_trans_FX

/-- info: 'RTKA.WFX.wmax_dist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.WFX.wmax_dist

/-- info: 'RTKA.WFX.wmax_of_good_hyp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.WFX.wmax_of_good_hyp

/-- info: 'RTKA.WFX.hyp_of_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.WFX.hyp_of_good

/-- info: 'RTKA.WFX.wmax_of_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.WFX.wmax_of_good

/-- info: 'RTKA.WFX.wmax_coll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.WFX.wmax_coll

/-- info: 'RTKA.wellFounded_FX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.wellFounded_FX

/-! 断片 `FY` の整列性は順序の仮定 `FYOrder` の下で示している（仮定はインスタンス引数で、公理ではない）。 -/

/-- info: 'RTKA.WFY.wmax_of_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.WFY.wmax_of_good

/-- info: 'RTKA.WFY.wmax_coll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.WFY.wmax_coll

/-- info: 'RTKA.wellFounded_FY' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.wellFounded_FY

/-- info: 'RTKA.lin_closedY' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.lin_closedY

/-- info: 'RTKA.instFYOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.instFYOrder

/-- info: 'RTKA.wellFounded_FY_NF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.wellFounded_FY_NF

/-- info: 'RTKA.Z.wellFounded_FZ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.Z.wellFounded_FZ

/-- info: 'RTKA.Z.lin_closedY' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.Z.lin_closedY

/-- info: 'RTKA.Z.instFZOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.Z.instFZOrder

/-- info: 'RTKA.Z.wellFounded_FZ_NF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.Z.wellFounded_FZ_NF

/-- info: 'RTKA.W.WFY.wmax_of_WNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.W.WFY.wmax_of_WNF

/-- info: 'RTKA.W.wellFounded_W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.W.wellFounded_W

/-- info: 'RTKA.W.lin_closedY' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.W.lin_closedY

/-- info: 'RTKA.W.instFWOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.W.instFWOrder

/-- info: 'RTKA.W.wellFounded_W_NF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.W.wellFounded_W_NF

/-- info: 'RTKA.wellFounded_isNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.wellFounded_isNF
