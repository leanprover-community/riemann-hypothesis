import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB

section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_mem_center_enveloping : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  first | exact @GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | exact GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | (intros; apply GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg <;> assumption)
end

section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.TraceCas

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth GlobalTheory.CompanionTheory.HCRep

theorem sum_sq_eq {L A ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [LieRing L] [LieAlgebra ℝ L]
    [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (B : LinearMap.BilinForm ℝ L) (hs : ∀ X Y, B X Y = B Y X) (l : L →ₗ[ℝ] A)
    (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (c c' : κ → L) (hc : ∀ Y, Y = ∑ k, B (c' k) Y • c k) :
    ∑ i, ε i • (l (b i) * l (b i)) = ∑ k, l (c k) * l (c' k) := by
  have h1 : ∀ i, l (b i) = ∑ k, B (c' k) (b i) • l (c k) := fun i => by
    conv_lhs => rw [hc (b i)]
    simp only [map_sum, map_smul]
  have h2 : ∀ k, l (c' k) = ∑ i, (ε i * B (b i) (c' k)) • l (b i) := fun k => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (c' k)]
    simp only [map_sum, map_smul]
  calc ∑ i, ε i • (l (b i) * l (b i))
      = ∑ i, ε i • ((∑ k, B (c' k) (b i) • l (c k)) * l (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h1 i]
    _ = ∑ k, l (c k) * ∑ i, (ε i * B (b i) (c' k)) • l (b i) := by
        simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hs (c' k) (b i)]
    _ = ∑ k, l (c k) * l (c' k) := Finset.sum_congr rfl fun k _ => by rw [← h2 k]

theorem half_sum {A : Type*} [Ring A] [Algebra ℂ A] (e₁ f₁ e₂ f₂ : A) :
    (2 : ℂ) • (((1 / 2 : ℂ) • (e₁ - Complex.I • f₁)) * ((1 / 2 : ℂ) • (e₂ - Complex.I • f₂)) +
      ((1 / 2 : ℂ) • (e₁ + Complex.I • f₁)) * ((1 / 2 : ℂ) • (e₂ + Complex.I • f₂))) =
      e₁ * e₂ - f₁ * f₂ := by
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, add_mul, mul_add, smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp

theorem mul_neg_add {A : Type*} [Ring A] (x y z t : A) : x * -y + z * t = z * t - x * y := by
  rw [mul_neg]
  abel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open Classical in
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  classical
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

theorem atEmb_neg (τ : E →+* ℂ) (z : ℂ) : atEmb τ (-z) = -atEmb τ z := by
  rw [atEmb_eq τ (-z), atEmb_eq τ z]
  simp only [Complex.neg_re, Complex.neg_im, neg_smul]
  abel

theorem place_formula (τ : E →+* ℂ) :
    (2 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) τ) + Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ))) =
      ∑ i, ∑ j, (lieS E a i j (atEmb τ 1) * lieS E a j i (atEmb τ 1) -
        lieS E a i j (atEmb τ Complex.I) * lieS E a j i (atEmb τ Complex.I)) := by
  have hc : ∀ i j : Fin a, Eop (a := a) (ComplexEmbedding.conjugate τ) i j =
      (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) + Complex.I • lieS E a i j (atEmb τ Complex.I)) := by
    intro i j
    simp only [Eop, atEmb_conj, map_one, Complex.conj_I, atEmb_neg, map_neg, smul_neg, sub_neg_eq_add]
  simp only [Formalism.REAL.Cas, hc, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact half_sum (A := Module.End ℂ (Sm E a)) (lieS E a i j (atEmb τ 1)) (lieS E a i j (atEmb τ Complex.I))
    (lieS E a j i (atEmb τ 1)) (lieS E a j i (atEmb τ Complex.I))

def cInv (z : Cinf E) : mixedEmbedding.mixedSpace E := (0, fun v => z v.1)

theorem cMap_cInv (z : Cinf E) : cMap E (cInv z) = z := rfl

theorem cInv_cMap (x : mixedEmbedding.mixedSpace E) : cInv (cMap E x) = x := by
  refine Prod.ext (funext fun v => ?_) rfl
  exact absurd (IsTotallyComplex.isComplex v.1) (InfinitePlace.not_isComplex_iff_isReal.2 v.2)

theorem mMap_injective : Function.Injective (mMap E a) := by
  intro X Y h
  funext p q
  have h' : cMap E ((X : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) p q) =
      cMap E ((Y : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) p q) := congrFun (congrFun h p) q
  have := congrArg cInv h'
  rwa [cInv_cMap, cInv_cMap] at this

def Mt (i j : Fin a) (x : Cinf E) : (isExpLieAlgebra E a).lieSubalgebra :=
  ⟨(Matrix.single i j (cInv x) : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), mem_lie _⟩

def coordL : (isExpLieAlgebra E a).lieSubalgebra →ₗ[ℝ] Lie E a where
  toFun X := mMap E a (X : ArchMatrix E a)
  map_add' X Y := map_add (mMap E a) (X : ArchMatrix E a) (Y : ArchMatrix E a)
  map_smul' r X := map_smul (mMap E a) r (X : ArchMatrix E a)

theorem coordL_Mt (i j : Fin a) (x : Cinf E) : coordL (Mt i j x) = toL (Matrix.single i j x) := by
  funext p q
  change cMap E (Matrix.single i j (cInv x) p q) = Matrix.single i j x p q
  simp only [Matrix.single_apply]
  split_ifs
  · exact cMap_cInv x
  · exact map_zero _

def liBL : (isExpLieAlgebra E a).lieSubalgebra →ₗ[ℝ] Module.End ℂ (Sm E a) := (lie E a).comp coordL

theorem liBL_apply (X : (isExpLieAlgebra E a).lieSubalgebra) : liBL X = liB X := rfl

theorem liBL_Mt (i j : Fin a) (x : Cinf E) : liBL (Mt i j x) = lieS E a i j x := by
  rw [lieS_apply]
  change lie E a (coordL (Mt i j x)) = _
  rw [coordL_Mt]

theorem trace_Mt (i j : Fin a) (x : Cinf E) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (Mt j i x) Y = ∑ w, (x w * coordL Y i j w).re := by
  have h : Matrix.trace (mat ((Mt j i x : (isExpLieAlgebra E a).lieSubalgebra) : ArchMatrix E a) *
      mat (Y : ArchMatrix E a)) = cInv x * mat (Y : ArchMatrix E a) i j := by
    change Matrix.trace (Matrix.single j i (cInv x) * mat (Y : ArchMatrix E a)) = _
    rw [Matrix.trace, Finset.sum_eq_single j]
    · simp [Matrix.diag, Matrix.single_mul_apply_same]
    · intro c _ hc
      exact Matrix.single_mul_apply_of_ne _ _ _ _ _ hc _
    · simp
  rw [archTraceForm_apply, h, mixedTraceL_apply]
  simp only [Prod.fst_mul, Pi.mul_apply, cInv, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Prod.snd_mul]
  refine Finset.sum_bij (fun v _ => v.1) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro w _
    exact ⟨⟨w, IsTotallyComplex.isComplex w⟩, by simp, rfl⟩
  · intro v _
    rfl

open Classical in
theorem toL_single_atEmb (i j p q : Fin a) (w v : InfinitePlace E) (z : ℂ) :
    toL (Matrix.single i j (atEmb w.embedding z)) p q v = if (w, i, j) = (v, p, q) then z else 0 := by
  change Matrix.single i j (atEmb w.embedding z) p q v = _
  simp only [Matrix.single_apply, Prod.mk.injEq]
  by_cases h1 : i = p <;> by_cases h2 : j = q <;> by_cases h3 : w = v <;>
    simp [h1, h2, h3, atEmb_embedding_apply, eq_comm]

def cc : (InfinitePlace E × Fin a × Fin a) × Bool → (isExpLieAlgebra E a).lieSubalgebra
  | ((w, i, j), false) => Mt i j (atEmb w.embedding 1)
  | ((w, i, j), true) => Mt i j (atEmb w.embedding Complex.I)

def cc' : (InfinitePlace E × Fin a × Fin a) × Bool → (isExpLieAlgebra E a).lieSubalgebra
  | ((w, i, j), false) => Mt j i (atEmb w.embedding 1)
  | ((w, i, j), true) => -Mt j i (atEmb w.embedding Complex.I)

theorem trace_cc'_false (w : InfinitePlace E) (i j : Fin a) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (cc' ((w, i, j), false)) Y = (coordL Y i j w).re := by
  classical
  change archTraceForm E a (Mt j i (atEmb w.embedding 1)) Y = _
  rw [trace_Mt]
  simp [atEmb_embedding_apply, apply_ite Complex.re]

theorem trace_cc'_true (w : InfinitePlace E) (i j : Fin a) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (cc' ((w, i, j), true)) Y = (coordL Y i j w).im := by
  classical
  change archTraceForm E a (-Mt j i (atEmb w.embedding Complex.I)) Y = _
  rw [map_neg, LinearMap.neg_apply, trace_Mt]
  simp [atEmb_embedding_apply, apply_ite Complex.re]

theorem expansion (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    Y = ∑ k, archTraceForm E a (cc' k) Y • cc k := by
  classical
  apply Subtype.ext
  apply mMap_injective
  change coordL Y = coordL (∑ k, archTraceForm E a (cc' k) Y • cc k)
  have term : ∀ (p q : Fin a) (v : InfinitePlace E) (t : InfinitePlace E × Fin a × Fin a),
      (∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b))) p q v =
        if t = (v, p, q) then coordL Y p q v else 0 := by
    rintro p q v ⟨w, i, j⟩
    rw [Fintype.sum_bool, map_smul, map_smul, trace_cc'_true, trace_cc'_false]
    change (((coordL Y i j w).im • coordL (Mt i j (atEmb w.embedding Complex.I)) +
      (coordL Y i j w).re • coordL (Mt i j (atEmb w.embedding 1))) p q v) = _
    rw [coordL_Mt, coordL_Mt]
    simp only [Pi.add_apply, Pi.smul_apply, toL_single_atEmb]
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ : w = v ∧ i = p ∧ j = q := by simpa using h
      apply Complex.ext <;> simp
    · simp
  rw [map_sum, Fintype.sum_prod_type]
  funext p q v
  let ev : Lie E a →+ ℂ := ⟨⟨fun X => X p q v, rfl⟩, fun _ _ => rfl⟩
  change ev (coordL Y) = ev (∑ t, ∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b)))
  rw [map_sum]
  change _ = ∑ t, (∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b))) p q v
  simp only [term]
  simp [ev]

theorem omegaOp_eq_two_cas (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have key := sum_sq_eq (A := Module.End ℂ (Sm E a)) (archTraceForm E a) archTraceForm_symm (liBL (E := E) (a := a)) b ε hε2 horth cc cc' expansion
  have hL : omegaOp (⇑b) ε = ∑ i, ε i • (liBL (b i) * liBL (b i)) := by
    unfold omegaOp
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [liBL_apply]
    ext φ
    simp
  rw [hL, key, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [place_formula, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  change liBL (Mt i j (atEmb w.embedding Complex.I)) * liBL (-Mt j i (atEmb w.embedding Complex.I)) +
    liBL (Mt i j (atEmb w.embedding 1)) * liBL (Mt j i (atEmb w.embedding 1)) = _
  rw [map_neg, liBL_Mt, liBL_Mt, liBL_Mt, liBL_Mt]
  exact mul_neg_add (A := Module.End ℂ (Sm E a)) _ _ _ _

end GlobalTheory.CompanionTheory.HCRep.TraceCas

end
end

section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_operator_eq_casimir_sum : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | exact GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | (intros; apply GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas <;> assumption)
end

section
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

section General

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_sq_map_eq {B : LinearMap.BilinForm ℝ L} {b : Module.Basis ι ℝ L} {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : L, B X Y = B Y X) (φ ψ : L →ₗ⁅ℝ⁆ L)
    (hφ : ∀ X Y, B (φ X) (φ Y) = B X Y) (hψ : ∀ X, φ (ψ X) = X) :
    ∑ j, ε j • (UniversalEnvelopingAlgebra.ι ℝ (φ (b j)) * UniversalEnvelopingAlgebra.ι ℝ (φ (b j))) =
      ∑ i, ε i • (UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i)) := by
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L)
  have h1 : ∀ j, u (φ (b j)) = ∑ i, (ε i * B (b i) (φ (b j))) • u (b i) := fun j => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (φ (b j))]
    simp only [map_sum, map_smul]
  have h2 : ∀ i, u (b i) = ∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j)) := fun i => by
    have e := congrArg φ (eq_sum_of_orthogonal hε horth (ψ (b i)))
    rw [hψ] at e
    conv_lhs => rw [e]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hφ (b j) (ψ (b i)), hψ]
  calc ∑ j, ε j • (u (φ (b j)) * u (φ (b j)))
      = ∑ j, ε j • (u (φ (b j)) * ∑ i, (ε i * B (b i) (φ (b j))) • u (b i)) :=
        Finset.sum_congr rfl fun j _ => by rw [← h1 j]
    _ = ∑ i, ∑ j, (ε i * (ε j * B (φ (b j)) (b i))) • (u (φ (b j)) * u (b i)) := by
        simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsymm (b i)]
        congr 1
        ring
    _ = ∑ i, ε i • ((∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j))) * u (b i)) := by
        simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
    _ = ∑ i, ε i • (u (b i) * u (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h2 i]

end General

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem archTraceForm_AdLie (g : archGroup E a) (X Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a ((isExpLieAlgebra E a).AdLie g X) ((isExpLieAlgebra E a).AdLie g Y) =
      archTraceForm E a X Y := by
  rw [archTraceForm_apply, archTraceForm_apply]
  congr 1
  have hgi : mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) *
      mat (((g : (ArchMatrix E a)ˣ)) : ArchMatrix E a) = 1 := by
    rw [← mat_mul]
    simp
  change Matrix.trace ((mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (X : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) *
    (mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (Y : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a))) = _
  generalize mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) = A at *
  generalize mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) = C at *
  generalize mat (X : ArchMatrix E a) = x
  generalize mat (Y : ArchMatrix E a) = y
  have e : A * x * C * (A * y * C) = A * (x * y * C) := by
    calc A * x * C * (A * y * C) = A * x * (C * A) * y * C := by simp only [Matrix.mul_assoc]
      _ = A * (x * y * C) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

theorem AdLie_AdLie_inv (g : archGroup E a) (X : (isExpLieAlgebra E a).lieSubalgebra) :
    (isExpLieAlgebra E a).AdLie g ((isExpLieAlgebra E a).AdLie g⁻¹ X) = X := by
  have e := (isExpLieAlgebra E a).Ad_inv_Ad g⁻¹ ((isExpLieAlgebra E a).ofLie X)
  rw [inv_inv] at e
  exact Subtype.ext (congrArg Subtype.val e)

theorem AdU_casimir {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0) (g : archGroup E a) :
    (isExpLieAlgebra E a).AdU g (casimir b ε) = casimir b ε := by
  simp only [casimir, map_sum, map_smul, map_mul, IsExpLieAlgebra.AdU_ι]
  exact sum_sq_map_eq hε horth archTraceForm_symm _ ((isExpLieAlgebra E a).AdLie g⁻¹)
    (archTraceForm_AdLie g) (AdLie_AdLie_inv g)

theorem toGL_surjective : Function.Surjective (toGL E a) := fun y => by
  refine ⟨archEquiv E a (Matrix.GeneralLinearGroup.map (infEq E).toRingHom y), ?_⟩
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  ext i j
  simp

theorem omegaOp_comm_rt (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  obtain ⟨u, rfl⟩ := toGL_surjective y
  rw [← infEmb_eq]
  have hrt : ∀ φ : Sm E a, smL E a (rt E a (infEmb E a u) φ) = rtInf u (smL E a φ) := fun _ => rfl
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, smL_omegaOp, hrt, uAction_rtInf,
    AdU_casimir b ε hε2 horth, hrt, smL_omegaOp]

end GlobalTheory.CompanionTheory.HCRep

end
end

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_operator_commutes_infinite_gl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    ∀ y : GL (Fin a) (Cinf E),
      GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  atlas_forward_decl GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt
end

section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_skew_curve {E : Type} [Field E] [NumberField E] {a : ℕ} (S : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL S) 0 ∧
      (S.conjTranspose = -S → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • S)).unit, Units.ext (by simp), ?_, fun hS t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) S (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hS, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • S)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem liB_skew_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  intro E _ _ _ a φ Z hZ hfd ψ hψ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hW
  have hst : ∀ k : Kinf E a, ∀ w ∈ W, cptRep E a k w ∈ W := by
    intro k w hw
    refine Submodule.span_induction (p := fun w _ => cptRep E a k w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      change cptRep E a (k * k') φ = cptRep E a k (cptRep E a k' φ)
      rw [map_mul, Module.End.mul_apply]
    · rw [map_zero]; exact W.zero_mem
    · intro x y _ _ hx hy; rw [map_add]; exact W.add_mem hx hy
    · intro r x _ hx; rw [map_smul]; exact W.smul_mem r hx
  let S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of (mMap E a (Z : ArchMatrix E a))
  have hS : S.conjTranspose = -S := by
    ext i j w
    have h := congrFun (congrFun hZ i) j
    have h2 := congrFun (congrArg Prod.snd h) ⟨w, IsTotallyComplex.isComplex w⟩
    exact h2
  obtain ⟨c, h0, hc, hu⟩ := exists_skew_curve S
  let W' : Submodule ℂ (GA E a → ℂ) := W.map (Sm E a).subtype
  have hW' : FiniteDimensional ℂ W' := inferInstance
  have hF : ∀ t, (fun g => ψ.1 (g * infGL E a (c t))) ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hS t⟩ ψ, hst _ _ hψ, funext fun g => by
      have e : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E a) = c t := Units.ext rfl
      change ψ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [e]⟩
  have hd : ∀ g : GA E a, HasDerivAt (fun t : ℝ => ψ.1 (g * infGL E a (c t))) ((liB Z ψ).1 g) 0 :=
    fun g => hasDerivAt_curve ψ g c (toL S) h0 hc
  obtain ⟨w, hw, e⟩ := AutomorphicForm.mem_of_hasDerivAt W' hF hd
  rwa [show liB Z ψ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.HCRep

end
end

section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_span_finite_dim_stable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span | exact GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span | (intros; apply GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span <;> assumption)
end

section
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.ConvLap

open Set Filter Topology MeasureTheory

section General

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤}

open IsExpLieAlgebra

theorem isSmoothFun_convDeriv {κ : G → ℂ}
    (hκ : h.IsSmoothFun κ) (X : 𝔤) :
    h.IsSmoothFun (h.convDeriv X κ) :=
  isSmoothFun_comp_inv (h := h) (κ := h.rightDeriv X fun z : G => κ z⁻¹)
    (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

theorem rightDeriv_eq_integral_convDeriv_of_conv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : h.IsSmoothFun κ) (hκc : HasCompactSupport κ)
    {f F : G → ℂ} (hfc : Continuous f) (hF : h.IsSmoothFun F)
    (hconv : ∀ x, F x = ∫ y, f (x * y) * κ y ∂μ) (X : 𝔤) (g : G) :
    h.rightDeriv X F g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X
  have hshift : ∀ t : ℝ, F (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv]
  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]
  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => F (g * h.expG (t • X))) (h.rightDeriv X F g) 0 :=
    h.hasDerivAt_rightDeriv hF X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end General

section Adelic

open AutomorphicForm

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem uAction_ι_eq_integral_convDeriv [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] {μ : MeasureTheory.Measure (archGroup K n)} [μ.IsHaarMeasure]
    (ψ u : archSmooth K n) {κ : archGroup K n → ℂ}
    (hκ : (isExpLieAlgebra K n).IsSmoothFun κ) (hκc : HasCompactSupport κ)
    (hu : ∀ g, (u : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ)
    (X : (isExpLieAlgebra K n).lieSubalgebra) (g : AdelicGLn.AdelicGL K n) :
    (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) *
        (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
  rw [uAction_ι_apply]
  have hconv : ∀ x, archSlice (u : AdelicGLn.AdelicGL K n → ℂ) g x =
      ∫ y, archSlice (ψ : AdelicGLn.AdelicGL K n → ℂ) g (x * y) * κ y ∂μ := by
    intro x
    simp only [archSlice_apply, map_mul, ← mul_assoc]
    exact hu _
  rw [rightDeriv_eq_integral_convDeriv_of_conv hκ hκc
    (IsExpLieAlgebra.continuous_of_isSmoothFun (ψ.2 g)) (u.2 g) hconv]
  simp only [archSlice_apply, one_mul]

theorem exists_kernel_uAction_uJ [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (μ : MeasureTheory.Measure (archGroup K n)) [μ.IsHaarMeasure]
    (ψ : archSmooth K n) (k : ℕ) :
    ∀ (J : Fin k → Fin (CuspidalSpectrum.archDim K n)) (u : archSmooth K n)
      (κ : archGroup K n → ℂ), (isExpLieAlgebra K n).IsSmoothFun κ → HasCompactSupport κ →
      (∀ g, (u : AdelicGLn.AdelicGL K n → ℂ) g =
        ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ) →
      ∃ D : archGroup K n → ℂ, (isExpLieAlgebra K n).IsSmoothFun D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) u :
            ↥(archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * D y ∂μ := by
  induction k with
  | zero =>
    intro J u κ hκ hκc hu
    refine ⟨κ, hκ, hκc, fun g => ?_⟩
    simpa [CuspidalSpectrum.uJ] using hu g
  | succ k ih =>
    intro J u κ hκ hκc hu
    set X := CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis K n (J 0)) with hX
    obtain ⟨D, hD, hDc, hrep⟩ := ih (Fin.tail J)
      (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u)
      ((isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ)
      (isSmoothFun_convDeriv hκ _) (IsExpLieAlgebra.hasCompactSupport_convDeriv hκc _)
      (fun g => uAction_ι_eq_integral_convDeriv ψ u hκ hκc hu X g)
    refine ⟨D, hD, hDc, fun g => ?_⟩
    rw [CuspidalSpectrum.uAction_uJ_succ]
    exact hrep g

theorem exists_conv_uJ_of_aeval_laplacian : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ψ : AutomorphicForm.archSmooth K n) (d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ),
    P.Monic → 0 < P.natDegree →
    (∀ g, Polynomial.aeval ((AutomorphicForm.isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (AutomorphicForm.sliceL g ψ) = 0) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
      (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
      (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
      ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) ψ :
            ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * AutomorphicForm.infEmb K n y) * D y ∂μ := by
  intro K _ _ n ψ d b P hPm hPd hP _ _ μ _ k J
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P
    hPm hPd Filter.univ_mem
  have h1 : ∀ g, (ψ : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ := by
    intro g
    have := hκ (sliceL g ψ) (hP g) 1
    simpa [archSlice_apply] using this
  obtain ⟨D, hD, hDc, hrep⟩ := exists_kernel_uAction_uJ μ ψ k J ψ κ hκs hκc h1
  exact ⟨D, IsExpLieAlgebra.continuous_of_isSmoothFun hD, hDc, hrep⟩

end Adelic

end GlobalTheory.CompanionTheory.HCRep.ConvLap
end
end

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplacian_monic_annihilator_measure : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ψ : AutomorphicForm.archSmooth K n) (d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ),
    P.Monic → 0 < P.natDegree →
    (∀ g, Polynomial.aeval ((AutomorphicForm.isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (AutomorphicForm.sliceL g ψ) = 0) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
      (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
      (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
      ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) ψ :
            ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * AutomorphicForm.infEmb K n y) * D y ∂μ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian
end

section
set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_monic_aeval_add {M : Type*} [AddCommGroup M] [Module ℂ M] (Ω T : Module.End ℂ M)
    (hc : Commute Ω T) (W : Submodule ℂ M) [FiniteDimensional ℂ W] (hT : ∀ w ∈ W, T w ∈ W)
    (q : Polynomial ℂ) (hq : q.Monic) (hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0) {v : M} (hv : v ∈ W) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (Ω + T) P v = 0 := by
  classical
  let V : Submodule ℂ M := ⨆ m : Fin (q.natDegree + 1), W.map (Ω ^ (m : ℕ))
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_iSup _
  have hmem : ∀ (i : ℕ), i < q.natDegree + 1 → ∀ w ∈ W, (Ω ^ i) w ∈ V := fun i hi w hw =>
    Submodule.mem_iSup_of_mem (⟨i, hi⟩ : Fin (q.natDegree + 1)) ⟨w, hw, rfl⟩
  have hpow : ∀ (m : ℕ), ∀ w ∈ W, (Ω ^ m) w ∈ V := by
    intro m w hw
    have e : (Ω ^ m) w = Polynomial.aeval Ω (Polynomial.X ^ m %ₘ q) w := by
      have h1 := Polynomial.modByMonic_add_div (Polynomial.X ^ m : Polynomial ℂ) q
      have h2 : Polynomial.aeval Ω (q * (Polynomial.X ^ m /ₘ q)) w = 0 := by
        rw [mul_comm, map_mul, Module.End.mul_apply, hqW w hw, map_zero]
      have h3 := congrArg (fun p => Polynomial.aeval Ω p w) h1
      simp only [map_add, LinearMap.add_apply, h2, add_zero, map_pow, Polynomial.aeval_X] at h3
      exact h3.symm
    rw [e, Polynomial.aeval_eq_sum_range' (n := q.natDegree + 1)
      (Nat.lt_succ_of_le (Polynomial.natDegree_modByMonic_le _ hq)), LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i hi => by
      rw [LinearMap.smul_apply]
      exact V.smul_mem _ (hmem i (Finset.mem_range.1 hi) w hw)
  have hst : ∀ x ∈ V, (Ω + T) x ∈ V := by
    intro x hx
    have hle : V ≤ V.comap (Ω + T) := by
      refine iSup_le fun m => ?_
      rintro _ ⟨w, hw, rfl⟩
      have e : (Ω + T) ((Ω ^ (m : ℕ)) w) = (Ω ^ ((m : ℕ) + 1)) w + (Ω ^ (m : ℕ)) (T w) := by
        rw [LinearMap.add_apply, pow_succ', Module.End.mul_apply, ← Module.End.mul_apply T,
          ((hc.pow_left (m : ℕ)).eq).symm, Module.End.mul_apply]
      change (Ω + T) ((Ω ^ (m : ℕ)) w) ∈ V
      rw [e]
      exact V.add_mem (hpow _ w hw) (hpow _ _ (hT w hw))
    exact hle hx
  have hv' : v ∈ V := by simpa using hpow 0 v hv
  exact AutomorphicForm.exists_monic_aeval_apply_eq_zero (Ω + T) V hst hv'

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_aeval_lapOp_eq_zero (φ : Sm E a) (hA : IsAutForm φ) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (hskew : ∀ i, ε i = -1 → b i ∈ archSkew E a) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (lapOp (⇑b)) P φ = 0 := by
  classical
  set Ω := omegaOp (E := E) (a := a) (⇑b) ε with hΩ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hWdef
  haveI : FiniteDimensional ℂ W := hA.kfin
  have hZ : Ω ∈ Zalg E a := by
    rw [hΩ, GlobalTheory.T.omega_operator_eq_casimir_sum  E a d b ε hε horth]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun w _ => Subalgebra.add_mem _ ?_ ?_) _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
  set Vz := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hVz
  haveI : FiniteDimensional ℂ Vz := hA.zfin
  have hVs : ∀ w ∈ Vz, Ω w ∈ Vz := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Ω w ∈ Vz) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨Ω * z, Subalgebra.mul_mem _ hZ hz, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hφV : φ ∈ Vz := Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩
  obtain ⟨q, hqm, -, hq⟩ := AutomorphicForm.exists_monic_aeval_apply_eq_zero Ω Vz hVs hφV
  have hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Polynomial.aeval Ω q w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      have hcomm : ∀ m, cptRep E a k (Ω m) = Ω (cptRep E a k m) := fun m =>
        (congrArg (fun T : Module.End ℂ (Sm E a) => T m)
          (GlobalTheory.T.omega_operator_commutes_infinite_gl E a d b ε hε horth (Unitary.toUnits k))).symm
      have := AutomorphicForm.map_aeval_apply_of_intertwine (cptRep E a k) hcomm q φ
      rw [hq, map_zero] at this
      exact this.symm
    · rw [map_zero]
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro c x _ hx; rw [map_smul, hx, smul_zero]
  have hlap : Commute Ω (lapOp (⇑b)) := by
    simp only [lapOp, Commute, SemiconjBy]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Ω * liB (b i) = liB (b i) * Ω := omegaOp_comm_liB b ε hε horth (b i)
    rw [← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  have hTW : ∀ w ∈ W, (lapOp (⇑b) - Ω) w ∈ W := by
    intro w hw
    have e : (lapOp (E := E) (a := a) (⇑b) - Ω) w =
        ∑ i, ((1 : ℂ) - (ε i : ℂ)) • liB (b i) (liB (b i) w) := by
      simp only [hΩ, lapOp, omegaOp, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      module
    rw [e]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases hε i with h | h
    · simp [h]
    · refine W.smul_mem _ ?_
      have hs := mem_archSkew.1 (hskew i h)
      have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := hA.kfin
      exact GlobalTheory.T.compact_span_finite_dim_stable E a φ (b i) hs hfd _ (GlobalTheory.T.compact_span_finite_dim_stable E a φ (b i) hs hfd _ hw)
  have hφW : φ ∈ W := by
    refine Submodule.subset_span ⟨1, ?_⟩
    change cptRep E a 1 φ = φ
    rw [map_one]
    rfl
  have hc : Commute Ω (lapOp (⇑b) - Ω) := by
    refine LinearMap.ext fun x => ?_
    have h2 := LinearMap.congr_fun hlap.eq x
    simp only [Module.End.mul_apply] at h2 ⊢
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h2]
  have hsum : Ω + (lapOp (⇑b) - Ω) = lapOp (⇑b) := LinearMap.ext fun x => by simp
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_monic_aeval_add Ω (lapOp (⇑b) - Ω) hc W hTW q hqm hqW hφW
  refine ⟨P, hP1, hP2, ?_⟩
  rwa [hsum] at hP3

theorem sliceL_aeval_lapOp {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra)
    (P : Polynomial ℂ) (ψ : Sm E a) (g : AdelicGLn.AdelicGL E a) :
    sliceL g (smL E a (Polynomial.aeval (lapOp (⇑b)) P ψ)) =
      Polynomial.aeval ((isExpLieAlgebra E a).laplacian (F := ℂ) b) P (sliceL g (smL E a ψ)) := by
  refine AutomorphicForm.map_aeval_apply_of_intertwine ((sliceL g).comp (smL E a)) (fun m => ?_) P ψ
  simp only [LinearMap.comp_apply, smL_lapOp, map_sum, sliceL_uAction,
    IsExpLieAlgebra.laplacian, LinearMap.sum_apply, Module.End.mul_apply,
    IsExpLieAlgebra.rightUAction_ι]

theorem uJ_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hs : φ.1 ∈ AutomorphicForm.archSmooth E a), IsAutForm φ → (∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup E a)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim E a)),
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL E a,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) k J) (⟨φ.1, hs⟩ : ↥(AutomorphicForm.archSmooth E a)) :
        ↥(AutomorphicForm.archSmooth E a)) : AdelicGLn.AdelicGL E a → ℂ) g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂μ) := by
  intro E _ _ _ a φ hs hA _ _ μ _ k J
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := E) (n := a)
  obtain ⟨P, hm, hd, hP⟩ := exists_aeval_lapOp_eq_zero φ hA b ε hε horth hskew
  exact GlobalTheory.T.laplacian_monic_annihilator_measure E a (smL E a φ) d b P hm hd
    (fun g => by rw [← sliceL_aeval_lapOp, hP, map_zero, map_zero]) μ k J

end GlobalTheory.CompanionTheory.HCRep

end
end
