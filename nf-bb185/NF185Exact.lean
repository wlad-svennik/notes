import EightMachine185
import Eight187Exact

namespace NFMachine185
open NF210 FFL FFL.FirstOrder

theorem halts_iff_nf_refutation : TM.Halts CS185.Table.machine CS185.Table.start ↔ (𝗡𝗙 ⊢ ⊥) :=
  halts_iff_eight_row_goal.trans Eight187.deriv_goal_iff_nf_refutation

end NFMachine185
#print axioms NFMachine185.halts_iff_nf_refutation
