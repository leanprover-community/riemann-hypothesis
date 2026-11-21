import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefInTranslate
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.NormalisedTranslate

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem delta_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : δ ≠ 0 := by
  intro h0
  subst h0
  have hz : lamOf D cc 0 = ⊥ := by
    unfold lamOf
    rw [AddSubgroup.closure_eq_bot_iff]
    rintro w ⟨c, -, rfl⟩
    simp
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  rw [B.lat, hz, AddSubgroup.mem_bot] at h1
  have h2 := B.L.indep.ne_zero 0
  exact h2 (by simpa using h1)



theorem kap_mem {D : D7} (T : Tor D) {N N' : ℕ} {La' : AddSubgroup (VC D N N')} (hI : IO.HfInt T La')
    {n : ℕ} (hn : n ≠ 0) {w x : VC D N N'} (hw : w ∈ La') (hx : n • x ∈ La') : kap D T w x ∈ Qbar := by
  obtain ⟨a, b, -, h⟩ := hI w hw _ hx
  have hb : (Hf D T w (n • x)).im = b := by rw [h]; simp
  rw [GlobalTheory.GalTheta.Hf_nsmul_right, ← Complex.ofReal_natCast, Complex.im_ofReal_mul] at hb
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have e : (Hf D T w x).im = (((b : ℚ) / (n : ℚ) : ℚ) : ℝ) := by
    push_cast
    rw [← hb]
    field_simp
  unfold kap
  rw [e, Complex.ofReal_ratCast]
  convert GlobalTheory.ThetaAlgebraic.exp_rat_mem (-2 * ((b : ℚ) / (n : ℚ))) using 2
  push_cast
  ring


end GlobalTheory.NormalisedTranslate
