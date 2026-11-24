module

public import Mathlib

@[expose] public section

open Polynomial Finset

namespace Bl.PowerApplication

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

theorem goal1 {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (p : ℂ[X]) :
    aeval T p f = p.eval z • f :=
  Module.End.aeval_apply_of_mem_apply_eq_smul hf

end Bl.PowerApplication
