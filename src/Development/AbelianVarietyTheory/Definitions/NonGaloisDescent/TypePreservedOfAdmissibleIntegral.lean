import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ReadingAllLemmas

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll.Model

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X}









variable (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

theorem zero_mem_ball (i : X.Tw) (j : ℕ) (b : Bool) {B : ℝ} (hB : 0 ≤ B) : (0 : Y.Fm i j b) ∈ Ball T i j b B :=
  ⟨zero_mem _, fun y => by simpa using hB⟩

theorem bsup_eq (i : X.Tw) (j : ℕ) (b : Bool) : Y.Bsup i j b = Submodule.span (X.O i) (Ball T i j b 1) :=
  T.Bsup_def i j b

theorem norm_l (i : X.Tw) : ‖((X.l i : ℕ) : ℂ_[X.l i])‖ = ((X.l i : ℝ))⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[X.l i] (PadicComplex (X.l i))), norm_algebraMap', Padic.norm_p]

theorem smul_l_pow (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b) :
    ((X.l i : X.O i) ^ c) • f = ((X.l i : FractionRing (X.O i)) ^ c) • f := by
  rw [← algebraMap_smul (FractionRing (X.O i))]
  simp

theorem l_pow_smul_mem (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (B : ℝ) (f : Y.Fm i j b)
    (hf : f ∈ Ball T i j b ((X.l i : ℝ) ^ c * B)) : ((X.l i : X.O i) ^ c) • f ∈ Ball T i j b B := by
  have hl : (0 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.pos
  rw [smul_l_pow]
  refine ⟨T.FmUr_smul i j b _ _ (pow_mem (natCast_mem _ _) _) hf.1, fun y => ?_⟩
  rw [T.ev_smul, norm_mul, map_pow, map_natCast, norm_pow, norm_l, inv_pow]
  rw [inv_mul_le_iff₀ (by positivity)]
  exact hf.2 y

theorem l_pow_smul_span (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b)
    (hf : f ∈ Submodule.span (X.O i) (Ball T i j b ((X.l i : ℝ) ^ c))) :
    ((X.l i : X.O i) ^ c) • f ∈ Y.Bsup i j b := by
  rw [bsup_eq T]
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (l_pow_smul_mem T i j b c 1 x (by simpa using hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx




theorem span_bsup_of_supBdd (h : SupBdd T) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) : Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b)) = ⊤ := by
  rw [eq_top_iff, ← T.FmUr_span i j b, Submodule.span_le]
  intro f hf
  obtain ⟨B, hB⟩ := h i hi j hj b f hf
  have hl : (1 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.one_lt
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt B hl
  have h1 : f ∈ Ball T i j b ((X.l i : ℝ) ^ c) := ⟨hB.1, fun y => (hB.2 y).trans hc.le⟩
  have h2 := l_pow_smul_span T i j b c f (Submodule.subset_span h1)
  rw [smul_l_pow] at h2
  have hne : ((X.l i : FractionRing (X.O i))) ≠ 0 := by
    intro h0
    have := congrArg (T.iC i) h0
    rw [map_natCast, map_zero] at this
    exact (X.lPrime i).out.ne_zero (by exact_mod_cast this)
  have h3 := (Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b))).smul_mem
    (((X.l i : FractionRing (X.O i)) ^ c)⁻¹) (Submodule.subset_span h2)
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul] at h3



theorem l_ne_zero (T : NTh D.R D.host D.what₂ D.LL0 N X Y) (i : X.Tw) : ((X.l i : FractionRing (X.O i))) ≠ 0 := by
  intro h0
  have := congrArg (T.iC i) h0
  rw [map_natCast, map_zero] at this
  exact (X.lPrime i).out.ne_zero (by exact_mod_cast this)



end GlobalTheory.TwAll.Model

end
