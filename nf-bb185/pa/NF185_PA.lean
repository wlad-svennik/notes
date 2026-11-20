import NF185PAMachineTransfer
import NF185PAIndependence

open FFL FFL.FirstOrder
open PA192.LiteralTM NF185PA

/-- Both formula codes refer to the published blank-tape transition tables. -/
example : M6.PA.theory ⊢ H192 🡒 H185 := machine_transfer

/-- The direct proof uses only the 185-state construction. -/
example : M6.PA.theory ⊢ (∼H185) 🡒 M6.PA.consistencySentence := internal_consistency

set_option pp.privateNames true
set_option pp.fullNames true
#print axioms NF185PA.machine_transfer
#print axioms NF185PA.internal_consistency
#print axioms NF185PA.pa_cannot_prove_nonhalting_of_consistent
#print axioms NF185PA.pa_independence
#print axioms NF185PA.true_value_independent
