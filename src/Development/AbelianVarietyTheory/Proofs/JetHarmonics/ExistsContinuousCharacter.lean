import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.CommutatorCharacter

variable {D : D7} {N N' : ℕ}



def vecHom (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Matrix (Fin N') (Fin N) D.host.E →+ VC D N N' :=
  AddMonoidHom.mk' (vecOf D cc δ) (GlobalTheory.PlaceComponents.vecOf_add D cc δ)

theorem vecHom_apply (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    vecHom cc δ A = vecOf D cc δ A := rfl

theorem continuous_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) {X : Type*} [TopologicalSpace X]
    (f : ZMod (p ^ n) → X) : Continuous fun a : ℤ_[p] => f (PadicInt.toZModPow n a) := by
  refine (IsLocallyConstant.comp (f := PadicInt.toZModPow n) ?_ f).continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have hp : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds a hp] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa [dist_eq_norm] using hy


end GlobalTheory.CommutatorCharacter
