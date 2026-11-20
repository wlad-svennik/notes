module
public import Counting192J
public import C193NFU
@[expose] public section
namespace Counting192J
open NF210
/-- A nonhalting blank tape for this exact table gives a model with full internal AxCount. -/
theorem nonhalting_implies_counting_model
    (h : ¬ TM.Halts CS192.Table.machine CS192.Table.start) : RangeNFU.HasCountingModel :=
  C193.counting_model_of_nonderivability (fun d => h (halts_iff_jpoint_goal.mpr d))
end Counting192J
#print axioms Counting192J.nonhalting_implies_counting_model
