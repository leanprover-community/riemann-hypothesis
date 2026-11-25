module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

noncomputable section

namespace GlobalTheory.ArchUniq.Coord

section Trace

variable {F : Type} [Field F] [NumberField F]

private theorem trace_pi_real_eq_sum' {ι : Type} [Fintype ι] (f : ι → ℝ) :
    Algebra.trace ℝ (ι → ℝ) f = ∑ i, f i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι)]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]

private theorem trace_pi_complex_eq_sum_two_mul_re {ι : Type} [Fintype ι] (f : ι → ℂ) :
    Algebra.trace ℝ (ι → ℂ) f = ∑ i, 2 * (f i).re := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => Complex.basisOneI)]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, Fintype.sum_sigma, Fin.sum_univ_two,
    Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem eq_zero_of_trace (x : mixedEmbedding.mixedSpace F)
    (h : ∀ b, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * b) = 0) : x = 0 := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h1 := h (Pi.single w 1, 0)
    rw [Algebra.trace_prod_apply, trace_pi_real_eq_sum', trace_pi_complex_eq_sum_two_mul_re] at h1
    simpa [Pi.single_apply] using h1
  · have h1 := h (0, Pi.single w (star (x.2 w)))
    rw [Algebra.trace_prod_apply, trace_pi_real_eq_sum', trace_pi_complex_eq_sum_two_mul_re] at h1
    have h2 : (x.2 w).re * (x.2 w).re + (x.2 w).im * (x.2 w).im = 0 := by
      simpa [Pi.single_apply, apply_ite Complex.re, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.star_def,
        Complex.mul_conj] using h1
    have hre : (x.2 w).re = 0 := by nlinarith [mul_self_nonneg (x.2 w).re, mul_self_nonneg (x.2 w).im]
    have him : (x.2 w).im = 0 := by nlinarith [mul_self_nonneg (x.2 w).re, mul_self_nonneg (x.2 w).im]
    show x.2 w = 0
    exact Complex.ext hre him

theorem isPairing_trP (κ : Type) [Fintype κ] : IsPairing (trP F κ) := by
  exact {
    addL x x' y := by
      simp only [trP, Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
    addR x y y' := by
      simp only [trP, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
    smulL c x y := by
      simp only [trP, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul]
    smulR c x y := by
      simp only [trP, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]
    nondegL x hx := by
      funext i
      apply eq_zero_of_trace
      intro b
      have h := hx (Pi.single i b)
      simpa [trP, Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h
    nondegR y hy := by
      funext i
      apply eq_zero_of_trace
      intro b
      have h := hy (Pi.single i b)
      simpa [trP, Pi.single_apply, ite_mul, Finset.sum_ite_eq', mul_comm] using h
  }

variable (F) in
def evH : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evI_eq (a : AF F) : evI F a = evH F a := rfl

theorem evI_realAd (c : ℝ) : evI F (realAd F c) = algebraMap ℝ _ c := by
  unfold evI realAd
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

variable {κ : Type}

theorem loc_lift (y : κ → mixedEmbedding.mixedSpace F) : locV (liftV y) = y := by
  funext i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)

theorem loc_add (x y : κ → AF F) : locV (x + y) = locV x + locV y := by
  funext i
  simp only [locV, Pi.add_apply, evI_eq, map_add (f := _)]

theorem loc_smul (c : ℝ) (x : κ → AF F) : locV (realAd F c • x) = c • locV x := by
  funext i
  simp only [locV, Pi.smul_apply, smul_eq_mul]
  rw [evI_eq, map_mul, ← evI_eq, ← evI_eq, evI_realAd, Algebra.smul_def]

theorem lift_add (x y : κ → mixedEmbedding.mixedSpace F) : liftV (x + y) = liftV x + liftV y := by
  funext i
  simp only [liftV, Pi.add_apply, map_add (f := _)]
  first
    | exact Prod.ext rfl (add_zero 0).symm

theorem lift_smul (c : ℝ) (x : κ → mixedEmbedding.mixedSpace F) : liftV (c • x) = realAd F c • liftV x := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul]
  simp only [liftV, realAd, LinearMap.inl_apply, Pi.smul_apply]
  rw [Algebra.smul_def, map_mul]
  first
    | exact Prod.ext rfl (mul_zero 0).symm

theorem lift_loc (x : κ → AF F) : liftV (locV x) = realAd F 1 • x := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul]
  simp only [liftV, locV, evI, RingEquiv.symm_apply_apply, realAd, LinearMap.inl_apply, map_one]
  exact Prod.ext (one_mul _).symm (zero_mul _).symm

end Trace

section Gram

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β p q : Type} [Fintype α] [Fintype β] [Fintype p] [Fintype q]

theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Gram

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

variable (M : Model σ X W)

def coordI (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  (locV (M.co.e u).1, locV (M.co.e u).2)

theorem coordI_add (u u' : Matrix (Fin n) (Fin d) (AE F E)) : coordI M (u + u') = coordI M u + coordI M u' := by
  first
    | simp only [coordI, map_add (f := _), Prod.fst_add, Prod.snd_add, loc_add, Prod.mk_add_mk]

theorem coordI_smul (c : ℝ) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    coordI M (realAd F c • u) = c • coordI M u := by
  first
    | simp only [coordI, map_smul, Prod.smul_fst, Prod.smul_snd, loc_smul, Prod.smul_mk]

theorem coordI_one (u : Matrix (Fin n) (Fin d) (AE F E)) : coordI M (realAd F 1 • u) = coordI M u := by
  rw [coordI_smul, one_smul]

theorem coordI_lift (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    coordI M (M.co.e.symm (liftV v.1, liftV v.2)) = v := by
  first
    | simp [coordI, loc_lift]

theorem lift_coordI (u : Matrix (Fin n) (Fin d) (AE F E)) :
    M.co.e.symm (liftV (coordI M u).1, liftV (coordI M u).2) = realAd F 1 • u := by
  first
    | (rw [coordI, lift_loc, lift_loc, ← Prod.smul_mk, Prod.mk.eta, ← map_smul, LinearEquiv.symm_apply_apply])

abbrev sympM (X : Spc F E n) (W : Spc F E d) := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)

theorem omega_coordI (u u' : Matrix (Fin n) (Fin d) (AE F E)) :
    omega (trP F (Fin n × Fin d)) (coordI M u) (coordI M u') =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evH F (sympM (σ := σ) X W u u')) := by
  rw [show sympM (σ := σ) X W u u' = _ from M.co.form u u']

  simp only [omega, trP, coordI, locV, dotProduct, map_sub, map_sum, map_mul, evI_eq]

end Model

end GlobalTheory.ArchUniq.Coord
