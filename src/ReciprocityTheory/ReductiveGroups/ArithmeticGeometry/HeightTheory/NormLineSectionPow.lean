import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
import ReciprocityTheory.SemistableReduction.ExistsDualDerivations
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.AlgStep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IrreducibleFactorStructure
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatDegreeLeAndCoeffProdPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PTNonempty

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

theorem algebraicIndependent_scaledForms {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (y : Fin (N + 1) → Ω) (jc : Fin (N + 1)) (hy : y jc = 1)
    (J : Fin D → Fin N) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (y (jc.succAbove (J b))) = if a = b then 1 else 0)
    (ρ : Option (Fin D) → Fin (D + 2)) (hρ : Function.Injective ρ) :
    AlgebraicIndependent K (Sum.elim
      (fun p : Fin (D + 2) × Fin (N + 1) =>
        (X (some p) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω))
      (fun o : Option (Fin D) => X none * ∑ j, X (some (ρ o, j)) * C (y j))) := by
  classical
  refine algebraicIndependent_of_derivations _ (Sum.elim
    (fun o => (pderiv o :
      Derivation Ω (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)
        (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)).restrictScalars K)
    (fun a => coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a))) ?_
  intro c H
  have hZ : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    intro o; simp [pderiv_X]
  have hpn : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (X none * ∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) =
        ∑ j, X (some (ρ o, j)) * C (y j) := by
    intro o; rw [Derivation.leibniz, hZ, smul_zero, zero_add, pderiv_X]; simp
  have hcd : ∀ a o, coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a)
      (X none * ∑ j, X (some (ρ o, j)) * C (y j)) =
        X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j)) := by
    intro a o
    simp [Derivation.leibniz, coeffDer_X, coeffDer_C, map_sum]
  let M : Matrix (Option (Fin D)) (Option (Fin D))
      (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) := fun r o =>
    match r with
    | none => ∑ j, X (some (ρ o, j)) * C (y j)
    | some a => X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j))
  have e1 : ∑ o, c (Sum.inr o) * ∑ j, (X (some (ρ o, j)) * C (y j) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    have := H (Sum.inl none)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, Derivation.coe_restrictScalars, hpn] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [pderiv_X]), zero_add] at this
  have e2 : ∀ a, ∑ o, c (Sum.inr o) * (X none * ∑ j, (X (some (ρ o, j)) * C (δ a (y j)) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)) = 0 := by
    intro a
    have := H (Sum.inr a)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, hcd] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [coeffDer_X]), zero_add] at this
  have hv : M.mulVec (fun o => c (Sum.inr o)) = 0 := by
    funext r
    cases r with
    | none =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e1]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
    | some a =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e2 a]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  let pt : Option (Fin (D + 2) × Fin (N + 1)) → Ω := fun v =>
    match v with
    | none => 1
    | some q => ∑ o : Option (Fin D), if ρ o = q.1 then
        (match o with
          | none => if q.2 = jc then 1 else 0
          | some b => (if q.2 = jc then -y (jc.succAbove (J b)) else 0) +
              (if q.2 = jc.succAbove (J b) then 1 else 0))
        else 0
  have hpt0 : ∀ j, pt (some (ρ none, j)) = if j = jc then 1 else 0 := by
    intro j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single none]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hpt1 : ∀ b j, pt (some (ρ (some b), j)) = (if j = jc then -y (jc.succAbove (J b)) else 0) +
      (if j = jc.succAbove (J b) then 1 else 0) := by
    intro b j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single (some b)]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hptn : pt none = 1 := rfl
  have hne : ∀ b, jc.succAbove (J b) ≠ jc := fun b => Fin.succAbove_ne jc (J b)
  have hev : (MvPolynomial.eval pt).mapMatrix M = 1 := by
    ext r o
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    cases r with
    | none =>
      cases o with
      | none => simp [M, hpt0, hy]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, Matrix.one_apply]
    | some a =>
      cases o with
      | none =>
        simp [M, hpt0, hy, hptn, Matrix.one_apply]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, hδ, Matrix.one_apply, hptn]
  have hdet : M.det ≠ 0 := by
    intro h0
    have := RingHom.map_det (MvPolynomial.eval pt) M
    rw [h0, map_zero, hev, Matrix.det_one] at this
    exact zero_ne_one this
  have hc2 : ∀ o, c (Sum.inr o) = 0 := fun o =>
    congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) o
  intro i
  rcases i with p | o
  · have := H (Sum.inl (some p))
    simpa [Fintype.sum_sum_type, hc2, pderiv_X, Pi.single_apply] using this
  · exact hc2 o

theorem scalarRatio_self {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V}
    (hf : f ≠ 0) : ratio (Ω := Ω) f f = 1 := by
  unfold ratio
  split_ifs with h
  · have hc : f = h.choose • f := h.choose_spec
    have h0 : (h.choose - 1) • f = 0 := by
      rw [sub_smul, one_smul, ← hc, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hf
  · exact absurd ⟨1, (one_smul Ω f).symm⟩ h

def hupa1Row (D : ℕ) (o : Option (Fin D)) : Fin (D + 2) := Fin.castSucc ((finSuccEquiv D).symm o)

def hupa1Eqv (D N : ℕ) :
    Option ((Fin (D + 2) × Fin (N + 1)) ⊕ Option (Fin D)) ≃ ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) where
  toFun v := match v with
    | none => Sum.inr (Fin.last (D + 1))
    | some (Sum.inl p) => Sum.inl p
    | some (Sum.inr o) => Sum.inr (hupa1Row D o)
  invFun v := match v with
    | Sum.inl p => some (Sum.inl p)
    | Sum.inr i => match finSuccEquivLast i with
      | none => none
      | some t => some (Sum.inr (finSuccEquiv D t))
  left_inv v := by
    rcases v with _ | p | o
    · simp
    · rfl
    · simp [hupa1Row]
  right_inv v := by
    rcases v with p | i
    · rfl
    · dsimp only
      rcases h : finSuccEquivLast i with _ | t
      · have : i = finSuccEquivLast.symm none := (Equiv.eq_symm_apply _).2 h
        simp [this]
      · have : i = finSuccEquivLast.symm (some t) := (Equiv.eq_symm_apply _).2 h
        simp [this, hupa1Row]

theorem optionEquivLeft_rename_some' {R S : Type*} [CommRing R] (a : MvPolynomial S R) :
    MvPolynomial.optionEquivLeft R S (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on
  next r => simp [MvPolynomial.optionEquivLeft_C]
  next p q hp hq => simp [hp, hq]
  next p s hp => simp [hp, MvPolynomial.optionEquivLeft_X_some]

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_ker_scaledSubstitution_le_one (hd : d.AxH 𝒜) (c : ι) : (RingHom.ker (d.scaledSubstitution c)).height ≤ 1 := by
  classical
  obtain ⟨J, hJ⟩ := hd.a1 c
  obtain ⟨δ, hδ⟩ := ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.exists_dual_derivations (K := K) (d.x c) J hJ
  have hy : d.affineCoord c (d.jc c) = 1 := scalarRatio_self (hd.w_base c)
  let ρ : Option (Fin d.D) → Fin (d.D + 2) := fun o =>
    (finSuccEquiv (d.D + 1)).symm (some ((finSuccEquiv d.D).symm o))
  have hρ : Function.Injective ρ := by
    intro o o' h
    simpa [ρ] using h
  have hind := algebraicIndependent_scaledForms (K := K) (d.affineCoord c) (d.jc c) hy J δ hδ ρ hρ
  let e : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2) ≃
      Option ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)) :=
    { toFun := fun x => match x with
        | Sum.inl p => some (Sum.inl p)
        | Sum.inr i => (finSuccEquiv (d.D + 1) i).map fun j => Sum.inr (finSuccEquiv d.D j)
      invFun := fun y => match y with
        | none => Sum.inr 0
        | some (Sum.inl p) => Sum.inl p
        | some (Sum.inr o) => Sum.inr (ρ o)
      left_inv := by
        rintro (p | i)
        · rfl
        · rcases h : finSuccEquiv (d.D + 1) i with _ | j <;>
          · have := (finSuccEquiv (d.D + 1)).symm_apply_apply i
            rw [h] at this
            simpa [h, ρ] using this
      right_inv := by
        rintro (_ | p | o)
        · simp
        · rfl
        · simp [ρ] }
  let g := (MvPolynomial.renameEquiv K e).trans
    (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)))
  let gr := g.toRingEquiv
  rw [← RingEquiv.height_comap gr.symm (RingHom.ker (d.scaledSubstitution c))]
  haveI hk : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _
  haveI : (Ideal.comap gr.symm (RingHom.ker (d.scaledSubstitution c))).IsPrime := Ideal.comap_isPrime _ _
  refine ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot _ ?_
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker] at ha
  rw [Ideal.mem_bot]
  have h2 : (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm
      (Polynomial.C a) = MvPolynomial.rename some a := by
    rw [AlgEquiv.symm_apply_eq]
    exact (optionEquivLeft_rename_some' a).symm
  have h1 : gr.symm (Polynomial.C a) = MvPolynomial.rename (fun s => e.symm (some s)) a := by
    show (MvPolynomial.renameEquiv K e).symm ((MvPolynomial.optionEquivLeft K
      ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm (Polynomial.C a)) = _
    rw [h2, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
    rfl
  rw [h1, scaledSubstitution_eq, MvPolynomial.aeval_rename] at ha
  have hfam : (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) ∘
      (fun s => e.symm (some s)) =
      Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun o => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (ρ o, j)) * MvPolynomial.C (d.affineCoord c j)) := by
    funext s
    rcases s with p | o <;> rfl
  rw [hfam] at ha
  exact (injective_iff_map_eq_zero _).mp hind a ha

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed

section

variable {K : Type} [Field K] [NumberField K] {κ : Type} [Fintype κ]

theorem map_ne_zero_of_ne_zero {f : MvPolynomial κ K} (hf : f ≠ 0) (σ : K →+* ℂ) :
    MvPolynomial.map σ f ≠ 0 := fun h => hf ((MvPolynomial.map_injective σ σ.injective) (by rw [h, map_zero]))

end

theorem logHeight_le_torusHeight {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) :
    h0 f ≤ hTX5 f := by
  unfold h0 hTX5
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine add_le_add le_rfl (Finset.sum_le_sum fun σ _ => ?_)
  exact sphereLeTorus B n a _ hn (map_ne_zero_of_ne_zero hf σ) (isMultiHomogeneous_map_ring a f ha σ)

theorem continuous_torusPoint' {κ : Type} : Continuous (fun θ : κ → ℝ => torusPoint θ) := by
  unfold torusPoint
  exact continuous_pi fun i => Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i)))

theorem measurable_log_eval_torus {κ : Type} [Fintype κ] (f : MvPolynomial κ ℂ) :
    Measurable (fun θ : κ → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) := (Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval f).comp continuous_torusPoint')).measurable)

theorem torusProb_map_comp {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) :
    Measure.map (fun θ : κ' → ℝ => θ ∘ e) (torusProb κ') = torusProb κ := by
  classical
  have hmeas : Measurable (fun θ : κ' → ℝ => θ ∘ e) :=
    measurable_pi_lambda _ (fun a => measurable_pi_apply (e a))
  unfold torusProb
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun θ : κ' → ℝ => θ ∘ e) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.extend e s (fun _ => Set.univ)) := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h y
      by_cases hy : ∃ a, e a = y
      · obtain ⟨a, rfl⟩ := hy
        rw [he.extend_apply]
        exact h a
      · rw [Function.extend_apply' _ _ _ hy]
        trivial
    · intro h a
      have h1 := h (e a)
      rwa [he.extend_apply] at h1
  rw [hpre, Measure.pi_pi]
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hν : ν Set.univ = 1 := by simp [ν]
  calc ∏ y, ν (Function.extend e s (fun _ => Set.univ) y)
      = ∏ y ∈ Finset.univ.image e, ν (Function.extend e s (fun _ => Set.univ) y) := by
        refine (Finset.prod_subset (Finset.subset_univ _) (fun y _ hy => ?_)).symm
        have hy' : ¬ ∃ a, e a = y := by simpa using hy
        rw [Function.extend_apply' _ _ _ hy', hν]
    _ = ∏ a, ν (s a) := by
        rw [Finset.prod_image (fun a _ b _ h => he h)]
        refine Finset.prod_congr rfl (fun a _ => ?_)
        rw [he.extend_apply]

theorem torusMean_rename {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) (f : MvPolynomial κ ℂ) :
    torusMean (MvPolynomial.rename e f) = torusMean f := by
  unfold torusMean
  simp_rw [MvPolynomial.eval_rename]
  rw [← torusProb_map_comp e he, MeasureTheory.integral_map]
  · rfl
  · exact (measurable_pi_lambda _ fun i => measurable_pi_apply (e i)).aemeasurable
  · exact (measurable_log_eval_torus f).aestronglyMeasurable

theorem gaussAbs_rename_of_injective {K : Type} [Field K] [NumberField K] {κ κ' : Type} (e : κ → κ')
    (he : Function.Injective e) (w : FinitePlace K) (f : MvPolynomial κ K) :
    gaussAbs w (MvPolynomial.rename e f) = gaussAbs w f := by
  classical
  unfold gaussAbs
  rw [MvPolynomial.support_rename_of_injective he, Finset.sup_image]
  congr 1
  refine Finset.sup_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, MvPolynomial.coeff_rename_mapDomain e he]

theorem hTX5_rename {K : Type} [Field K] [NumberField K] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ → κ') (he : Function.Injective e) (f : MvPolynomial κ K) :
    hTX5 (MvPolynomial.rename e f) = hTX5 f := by
  unfold hTX5
  congr 2
  · exact finsum_congr fun w => by rw [gaussAbs_rename_of_injective e he w f]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [MvPolynomial.map_rename, torusMean_rename e he]

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

section CoeffIn

variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]

noncomputable def asPolyInVar (i : V) : MvPolynomial V R →ₐ[R] Polynomial (MvPolynomial V R) :=
  MvPolynomial.aeval fun v => if v = i then Polynomial.X else Polynomial.C (MvPolynomial.X v)

theorem coeffIn_eq_sum (i : V) (k : ℕ) (P : MvPolynomial V R) (S : Finset (V →₀ ℕ))
    (hS : P.support ⊆ S) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k P =
      ∑ s ∈ S, if s i = k then MvPolynomial.monomial (s.erase i) (P.coeff s) else 0 := by
  unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
  rw [Finset.sum_filter]
  apply Finset.sum_subset hS
  intro s _ hs
  rw [MvPolynomial.notMem_support_iff.mp hs]
  simp

theorem coeffIn_add_alt (i : V) (k : ℕ) (p q : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k (p + q) = ReciprocityTheory.MultiplicativeHeights.coeffIn i k p + ReciprocityTheory.MultiplicativeHeights.coeffIn i k q := by
  classical
  rw [coeffIn_eq_sum i k _ _ MvPolynomial.support_add,
    coeffIn_eq_sum i k p (p.support ∪ q.support) Finset.subset_union_left,
    coeffIn_eq_sum i k q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [MvPolynomial.coeff_add, map_add]

theorem polyIn_monomial_of_eq_zero (i : V) (t : V →₀ ℕ) (ht : t i = 0) (a : R) :
    asPolyInVar i (MvPolynomial.monomial t a) = Polynomial.C (MvPolynomial.monomial t a) := by
  rw [asPolyInVar, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Polynomial.C_mul,
    Finsupp.prod, Finsupp.prod, map_prod, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvi : v ≠ i := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hv) ht
  rw [if_neg hvi, map_pow]

theorem polyIn_monomial (i : V) (u : V →₀ ℕ) (a : R) :
    asPolyInVar i (MvPolynomial.monomial u a) =
      Polynomial.C (MvPolynomial.monomial (u.erase i) a) * Polynomial.X ^ (u i) := by
  have hu : u = Finsupp.single i (u i) + u.erase i := (Finsupp.single_add_erase i u).symm
  have e : MvPolynomial.monomial u a =
      MvPolynomial.monomial (Finsupp.single i (u i)) (1 : R) * MvPolynomial.monomial (u.erase i) a := by
    conv_lhs => rw [hu]
    rw [MvPolynomial.monomial_mul, one_mul]
  rw [e, map_mul, polyIn_monomial_of_eq_zero i (u.erase i) (by simp) a,
    ← MvPolynomial.X_pow_eq_monomial,
    map_pow, asPolyInVar, MvPolynomial.aeval_X, if_pos rfl, mul_comm]

theorem coeffIn_eq_polyIn_coeff (i : V) (k : ℕ) (P : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k P = (asPolyInVar i P).coeff k := by
  classical
  refine MvPolynomial.induction_on' P (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [coeffIn_eq_sum i k _ {u} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, polyIn_monomial, Polynomial.coeff_C_mul_X_pow]
    by_cases h : u i = k
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · rw [coeffIn_add_alt, map_add, Polynomial.coeff_add, hp, hq]

theorem coeffIn_map {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) (i : V)
    (k : ℕ) (P : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k (MvPolynomial.map φ P) =
      MvPolynomial.map φ (ReciprocityTheory.MultiplicativeHeights.coeffIn i k P) := by
  unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
  rw [MvPolynomial.support_map_of_injective _ hφ, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.coeff_map]

end CoeffIn

theorem gaussAbs_coeffIn_le {V : Type*} (w : FinitePlace K) (i : V) (k : ℕ)
    (P : MvPolynomial V K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (ReciprocityTheory.MultiplicativeHeights.coeffIn i k P) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w P := by
  classical
  have h0 : 0 ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w P := by unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs; exact NNReal.coe_nonneg _
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le w _ h0 fun t => ?_
  unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
  rw [MvPolynomial.coeff_sum]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le w _ _ h0 fun s _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w P s
  · rw [map_zero]; exact h0

theorem coeff_prod_pow_linear {B : Type*} [CommRing B] {T : Type*} (s : Finset T) (p : T → Polynomial B)
    (e : T → ℕ) (hp : ∀ t, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  first | exact GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow .. | (apply GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (intros; apply GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (intros; apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> first | assumption | infer_instance)

theorem polyIn_substitution_leading {D N : ℕ} (f : KTp K D N) (a : Fin (D + 1) → ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) :
    (asPolyInVar (Sum.inr 0) (bilinearSubstitution f)).natDegree ≤ ∑ b, a b ∧
      (asPolyInVar (Sum.inr 0) (bilinearSubstitution f)).coeff (∑ b, a b) =
        MvPolynomial.rename (fun t : TVar D N =>
          (Sum.inl (t.1.succ, t.2) : (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2))) f := by
  classical
  set E := asPolyInVar (R := K) (V := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) (Sum.inr 0)
  let p : TVar D N → Polynomial (MvPolynomial ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) K) :=
    fun t => E (MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
      MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2)))
  have hpt : ∀ t, p t = Polynomial.X * Polynomial.C (MvPolynomial.X (Sum.inl (t.1.succ, t.2))) -
      Polynomial.C (MvPolynomial.X (Sum.inr t.1.succ)) *
        Polynomial.C (MvPolynomial.X (Sum.inl (0, t.2))) := by
    intro t
    simp [p, E, asPolyInVar, Fin.succ_ne_zero]
  have hp1 : ∀ t, (p t).natDegree ≤ 1 := by
    intro t
    rw [hpt]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  have hpc : ∀ t, (p t).coeff 1 = MvPolynomial.X (Sum.inl (t.1.succ, t.2)) := by
    intro t
    rw [hpt]
    simp [Polynomial.coeff_C]
  have hEG : E (bilinearSubstitution f) = MvPolynomial.aeval p f := by
    unfold bilinearSubstitution
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hsum : ∀ s ∈ f.support, ∑ t, s t = ∑ b, a b := by
    intro s hs
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => hmh s hs b
  have hterm : ∀ s ∈ f.support,
      (MvPolynomial.aeval p (MvPolynomial.monomial s (f.coeff s))).natDegree ≤ ∑ b, a b ∧
        (MvPolynomial.aeval p (MvPolynomial.monomial s (f.coeff s))).coeff (∑ b, a b) =
          MvPolynomial.rename (fun t : TVar D N =>
            (Sum.inl (t.1.succ, t.2) : (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)))
            (MvPolynomial.monomial s (f.coeff s)) := by
    intro s hs
    obtain ⟨h1, h2⟩ := coeff_prod_pow_linear Finset.univ p s hp1
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Polynomial.algebraMap_apply, ← hsum s hs]
    refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans h1, ?_⟩
    rw [Polynomial.coeff_C_mul, h2, MvPolynomial.rename_monomial, MvPolynomial.monomial_eq,
      MvPolynomial.algebraMap_eq]
    congr 1
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact Finset.prod_congr rfl fun t _ => by rw [hpc]
  rw [hEG]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum]
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => (hterm s hs).1, ?_⟩
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun s hs => (hterm s hs).2

theorem logHeight_le_torusHeight_subst {D N : ℕ} (f : KTp K D N) (hf : f ≠ 0) (a : Fin (D + 1) → ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) : ReciprocityTheory.MultiplicativeHeights.h0 f ≤ hTX5 (bilinearSubstitution f) := by
  classical
  set ρ : TVar D N → (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2) := fun t => Sum.inl (t.1.succ, t.2)
  have hρ : Function.Injective ρ := by
    intro t t' h
    simp only [ρ, Sum.inl.injEq, Prod.mk.injEq, Fin.succ_inj] at h
    exact Prod.ext h.1 h.2
  obtain ⟨hdeg, htop⟩ := polyIn_substitution_leading f a hmh
  have hc : ReciprocityTheory.MultiplicativeHeights.coeffIn (Sum.inr 0) (∑ b, a b) (bilinearSubstitution f) = MvPolynomial.rename ρ f := by
    rw [coeffIn_eq_polyIn_coeff, htop]
  have hc' : ∀ k, ∑ b, a b < k → ReciprocityTheory.MultiplicativeHeights.coeffIn (Sum.inr 0) k (bilinearSubstitution f) = 0 := by
    intro k hk
    rw [coeffIn_eq_polyIn_coeff]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hk)
  have hR0 : MvPolynomial.rename ρ f ≠ 0 := fun h0 =>
    hf (MvPolynomial.rename_injective ρ hρ (by rw [h0, map_zero]))
  have hG0 : bilinearSubstitution f ≠ 0 := by
    intro h0
    apply hR0
    rw [← hc, h0]
    unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
    simp
  have h1 : ReciprocityTheory.MultiplicativeHeights.h0 f ≤ hTX5 f := logHeight_le_torusHeight (Nat.succ_pos N) a f hf hmh
  refine h1.trans ?_
  rw [← hTX5_rename ρ hρ f]
  unfold hTX5
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine add_le_add ?_ (Finset.sum_le_sum fun φ _ => ?_)
  · refine finsum_le_finsum' (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hR0)
      (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hG0) fun w => ?_
    refine Real.log_le_log (ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w _ hR0) ?_
    rw [← hc]
    exact gaussAbs_coeffIn_le w _ _ _
  · have hinj := MvPolynomial.map_injective φ φ.injective
      (σ := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2))
    have e1 : ReciprocityTheory.MultiplicativeHeights.coeffIn (Sum.inr 0) (∑ b, a b) (MvPolynomial.map φ (bilinearSubstitution f)) =
        MvPolynomial.map φ (MvPolynomial.rename ρ f) := by
      rw [coeffIn_map φ φ.injective, hc]
    have hne : ReciprocityTheory.MultiplicativeHeights.coeffIn (Sum.inr 0) (∑ b, a b) (MvPolynomial.map φ (bilinearSubstitution f)) ≠ 0 := by
      rw [e1]
      intro h0
      exact hR0 (hinj (by rw [h0, map_zero]))
    have := ReciprocityTheory.MultiplicativeHeights.Closed.torusCoeff _ (MvPolynomial.map φ (bilinearSubstitution f)) (Sum.inr 0) (∑ b, a b) hne
      (Or.inl fun k hk => by rw [coeffIn_map φ φ.injective, hc' k hk, map_zero])
    rwa [e1] at this

theorem gaussAbs_monomial {σ : Type*} (w : FinitePlace K) (s : σ →₀ ℕ) (κ : K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.monomial s κ) = w κ := by
  classical
  apply le_antisymm
  · refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le w _ (apply_nonneg w κ) fun t => ?_
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact le_rfl
    · rw [map_zero]; exact apply_nonneg w κ
  · have := ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w (MvPolynomial.monomial s κ) s
    rwa [MvPolynomial.coeff_monomial, if_pos rfl] at this

theorem sum_log_abs_eq_zero (κ : K) (hκ : κ ≠ 0) :
    ∑ᶠ w : FinitePlace K, Real.log (w κ) + ∑ φ : K →+* ℂ, Real.log ‖φ κ‖ = 0 := by
  have hmul : (Function.mulSupport fun w : FinitePlace K => w κ).Finite :=
    FinitePlace.hasFiniteMulSupport hκ
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w κ) = Real.log (∏ᶠ w : FinitePlace K, w κ) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hκ).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ κ‖ = Real.log |Algebra.norm ℚ κ| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hκ))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ κ)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ κ‖) (fun φ => ‖φ κ‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hκ]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem hTX5_C_mul_X_pow_mul_pow {σ : Type} [Fintype σ] (κ : K) (hκ : κ ≠ 0) (v : σ) (a m : ℕ)
    (F1 : MvPolynomial σ K) (hF1 : F1 ≠ 0) :
    hTX5 (MvPolynomial.C κ * MvPolynomial.X v ^ a * F1 ^ m) = m * hTX5 F1 := by
  classical
  have hP : MvPolynomial.C κ * MvPolynomial.X v ^ a =
      MvPolynomial.monomial (Finsupp.single v a) κ := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hM0 : MvPolynomial.monomial (Finsupp.single v a) κ ≠ 0 := by
    rw [Ne, MvPolynomial.monomial_eq_zero]; exact hκ
  have hpow : ∀ k : ℕ, F1 ^ k ≠ 0 := fun k => pow_ne_zero k hF1
  have hgpow : ∀ (w : FinitePlace K) (k : ℕ),
      ReciprocityTheory.MultiplicativeHeights.gaussAbs w (F1 ^ k) = ReciprocityTheory.MultiplicativeHeights.gaussAbs w F1 ^ k := by
    intro w k
    induction k with
    | zero => rw [pow_zero, pow_zero, ← MvPolynomial.C_1, MvPolynomial.C_apply, gaussAbs_monomial,
        map_one]
    | succ k ih => rw [pow_succ, pow_succ, ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul w _ _ (hpow k) hF1, ih]
  have hgauss : ∀ w : FinitePlace K,
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C κ * MvPolynomial.X v ^ a * F1 ^ m)) =
        Real.log (w κ) + m * Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w F1) := by
    intro w
    rw [hP, ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul w _ _ hM0 (hpow m), gaussAbs_monomial, hgpow,
      Real.log_mul, Real.log_pow]
    · exact (FinitePlace.pos_iff.2 hκ).ne'
    · exact (pow_pos (ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w F1 hF1) m).ne'
  have hfinκ : (Function.support fun w : FinitePlace K => Real.log (w κ)).Finite := by
    have := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite (MvPolynomial.monomial (Finsupp.single v a) κ) hM0
    simpa only [gaussAbs_monomial] using this
  have hfinF := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite F1 hF1
  have hfinsum : ∑ᶠ w : FinitePlace K,
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C κ * MvPolynomial.X v ^ a * F1 ^ m)) =
      ∑ᶠ w : FinitePlace K, Real.log (w κ) +
        m * ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w F1) := by
    simp_rw [hgauss]
    rw [finsum_add_distrib hfinκ (hfinF.subset (Function.support_mul_subset_right _ _)),
      mul_finsum' _ _ hfinF]
  have TB := ReciprocityTheory.MultiplicativeHeights.Closed.torusMeanBasic
  have htor : ∀ φ : K →+* ℂ,
      ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map φ (MvPolynomial.C κ * MvPolynomial.X v ^ a * F1 ^ m)) =
        Real.log ‖φ κ‖ + m * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map φ F1) := by
    intro φ
    have hinj := MvPolynomial.map_injective φ φ.injective (σ := σ)
    have hF1' : MvPolynomial.map φ F1 ≠ 0 := fun h => hF1 (hinj (by rw [h, map_zero]))
    have hpow' : ∀ k : ℕ, (MvPolynomial.map φ F1) ^ k ≠ 0 := fun k => pow_ne_zero k hF1'
    have hmon0 : MvPolynomial.monomial (Finsupp.single v a) (φ κ) ≠ 0 := by
      rw [Ne, MvPolynomial.monomial_eq_zero]; exact (map_ne_zero φ).2 hκ
    have hp : ∀ k : ℕ, ReciprocityTheory.MultiplicativeHeights.torusMean ((MvPolynomial.map φ F1) ^ k) =
        k * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map φ F1) := by
      intro k
      induction k with
      | zero =>
        rw [pow_zero, ← MvPolynomial.C_1, MvPolynomial.C_apply, (TB σ).2.2]
        simp
      | succ k ih =>
        rw [pow_succ, (TB σ).2.1 _ _ (hpow' k) hF1', ih]
        push_cast
        ring
    rw [hP, map_mul, map_pow, MvPolynomial.map_monomial, (TB σ).2.1 _ _ hmon0 (hpow' m), (TB σ).2.2,
      hp]
  unfold hTX5
  rw [hfinsum]
  simp_rw [htor]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_div_assoc']
  congr 1
  linear_combination sum_log_abs_eq_zero κ hκ

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

abbrev UXVar (D N : ℕ) : Type := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)

def xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) : ℕ := ∑ i, s (Sum.inr i)

def uDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) : ℕ := ∑ p, s (Sum.inl p)

def XHom {R : Type*} [CommSemiring R] {D N : ℕ} (n : ℕ) (Q : MvPolynomial (UXVar D N) R) : Prop :=
  ∀ s ∈ Q.support, xDeg s = n

def UDegLE {R : Type*} [CommSemiring R] {D N : ℕ} (n : ℕ) (Q : MvPolynomial (UXVar D N) R) :
    Prop :=
  ∀ s ∈ Q.support, uDeg s ≤ n

noncomputable def hT {κ : Type} [Fintype κ] (f : MvPolynomial κ K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w f)) +
      ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def evc (c : ι) :
    MvPolynomial (UXVar d.D d.N) K →ₐ[K] MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (A c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X p
    | Sum.inr i => ∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (d.w j c)

noncomputable def laW : ℝ := meanK fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))

noncomputable def upB : ℝ :=
  d.PP0' * d.wsize d.wL + max 0 d.laW + Real.log (d.N + 1 : ℕ) + 1

theorem lineSection_eq_ratio_smul (hd : d.AxH 𝒜) (c : ι) (j : Fin (d.N + 1)) :
    d.w j c = d.affineCoord c j • d.w (d.jc c) c := by
  exact d.w_eq_scalarRatio_smul hd c j

theorem lineSection_pow_ne_zero (hd : d.AxH 𝒜) (c : ι) (n : ℕ) : d.w (d.jc c) c ^ n ≠ 0 := by
  haveI := hd.graded c
  have hw := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  induction n with
  | zero =>
    rw [pow_zero]
    haveI : Nontrivial (A c) := ⟨⟨_, _, hw0⟩⟩
    exact one_ne_zero
  | succ n ih =>
    rw [pow_succ]
    exact hd.mul_ne_zero c (SetLike.pow_mem_graded n hw) hw ih hw0

private theorem sum_support_inr_eq_xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) :
    ∑ x ∈ s.support, Sum.elim (fun _ => 0) (fun i => s (Sum.inr i)) x = xDeg s := by
  rw [xDeg, Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]
  · simp
  · intro x _ hx
    cases x with
    | inl p => rfl
    | inr i => simpa using hx

theorem lineEval_eq_zero_iff (hd : d.AxH 𝒜) (c : ι) (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K)
    (hQ : XHom n Q) : d.evc c Q = 0 ↔ d.linearSubstitution c Q = 0 := by
  haveI := hd.tower c
  have hw0 := d.lineSection_pow_ne_zero hd c n
  have hfac : d.evc c Q = MvPolynomial.map (algebraMap (Ω c) (A c)) (d.linearSubstitution c Q) *
      MvPolynomial.C (d.w (d.jc c) c ^ n) := by
    rw [Q.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [evc, linearSubstitution, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_apply, map_mul,
      MvPolynomial.map_C, Finsupp.prod, map_prod, map_pow]
    rw [← IsScalarTower.algebraMap_apply, mul_assoc]
    congr 1
    rw [← hQ s hs, ← sum_support_inr_eq_xDeg s]
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    cases x with
    | inl p => simp
    | inr i =>
      simp only [Sum.elim_inr, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
      rw [← mul_pow, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [d.lineSection_eq_ratio_smul hd c j, Algebra.smul_def, MvPolynomial.C_mul]
      ring
  rw [hfac]
  constructor
  · intro h
    ext β
    have hb := congrArg (MvPolynomial.coeff β) h
    rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero, mul_comm,
      ← Algebra.smul_def] at hb
    rw [MvPolynomial.coeff_zero]
    exact (smul_eq_zero.1 hb).resolve_right hw0
  · intro h
    rw [h, map_zero, zero_mul]

theorem irreducible_factor_height_bound (hd : d.AxH 𝒜) (h : d.S1) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 (F c)) :
    ∃ (F1 : MvPolynomial (UXVar d.D d.N) K) (m deF : ℕ), 1 ≤ m ∧ 1 ≤ deF ∧
      m * deF ≤ d.delc c ∧ Irreducible F1 ∧ XHom deF F1 ∧ UDegLE ((d.D + 1) * d.delc c) F1 ∧
      ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ m * hT F1 ∧
      ∀ (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K), XHom n Q → (d.evc c Q = 0 ↔ F1 ∣ Q) := by
  obtain ⟨F1, κ, a, m, deF, hκ, hm, hmd, hirr, hx, hu, hG, hphiG, hmh⟩ :=
    d.irreducible_factor_structure hd h F hF c hpos
  have hy : d.affineCoord c (d.jc c) ≠ 0 := by
    intro h0
    apply hd.w_base c
    have e := d.lineSection_eq_ratio_smul hd c (d.jc c)
    rw [h0, zero_smul] at e
    exact e
  have hx0 : d.linearSubstitution c (MvPolynomial.X (Sum.inr 0)) ≠ 0 := by
    intro h0
    have e := congrArg (MvPolynomial.eval (fun p : Fin (d.D + 2) × Fin (d.N + 1) =>
      if p = (0, d.jc c) then (1 : Ω c) else 0)) h0
    simp [linearSubstitution] at e
    exact hy e
  have hκ' : d.linearSubstitution c (MvPolynomial.C κ) ≠ 0 := by
    simp [linearSubstitution, hκ]
  have hF1 : d.linearSubstitution c F1 = 0 := by
    rw [hG, map_mul, map_mul, map_pow, map_pow] at hphiG
    simp only [mul_eq_zero, pow_eq_zero_iff', hκ', hx0, false_and, false_or] at hphiG
    exact hphiG.1
  have hF1ne : F1 ≠ 0 := hirr.ne_zero
  have hspan : (Ideal.span {F1}).IsPrime := (Ideal.span_singleton_prime hF1ne).mpr hirr.prime
  have hle : Ideal.span {F1} ≤ RingHom.ker (d.scaledSubstitution c) := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, d.scaledSubstitution_of_homogeneous c deF F1 hx, hF1,
      map_zero, mul_zero]
  have hPp : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _
  have heq : Ideal.span {F1} = RingHom.ker (d.scaledSubstitution c) := by
    by_contra hne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    have h2 := d.height_ker_scaledSubstitution_le_one hd c
    have h3 : (Ideal.span {F1}).height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
      exact hF1ne
    have h4 : 1 ≤ (Ideal.span {F1}).height := Order.one_le_iff_ne_zero.mpr h3
    have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h1.trans h2)
    exact absurd h5 (by norm_num)
  have hdeF : 1 ≤ deF := by
    by_contra h0
    have h0' : deF = 0 := by omega
    exact hF1ne (d.eq_zero_of_xhom_zero c F1 (fun s hs => (hx s hs).trans h0') hF1)
  have hkey : ∀ (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K), XHom n Q →
      (d.evc c Q = 0 ↔ F1 ∣ Q) := by
    intro n Q hQ
    rw [d.lineEval_eq_zero_iff hd c n Q hQ, ← Ideal.mem_span_singleton, heq, RingHom.mem_ker,
      d.scaledSubstitution_of_homogeneous c n Q hQ]
    constructor
    · intro h0
      rw [h0, map_zero, mul_zero]
    · intro h0
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd (pow_eq_zero_iff'.mp h1).1 (MvPolynomial.X_ne_zero _)
      · exact MvPolynomial.rename_injective _ (Option.some_injective _) (by rw [h1, map_zero])
  have hFne : F c ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp [ReciprocityTheory.MultiplicativeHeights.h0, ReciprocityTheory.MultiplicativeHeights.gaussAbs, ReciprocityTheory.MultiplicativeHeights.blockSphereMean] at hpos
  have hh : ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ m * hT F1 := by
    have e1 := logHeight_le_torusHeight_subst (F c) hFne _ hmh
    rw [hG, hTX5_C_mul_X_pow_mul_pow κ hκ _ a m F1 hF1ne] at e1
    exact e1
  exact ⟨F1, m, deF, hm, hdeF, hmd, hirr, hx, hu, hh, hkey⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

theorem card_support_le {R : Type*} [CommSemiring R] {D N n n' : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) (hu : UDegLE n' Q) :
    Q.support.card ≤
      (n + D + 1).choose (D + 1) * (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) := by
  classical
  let fx : (UXVar D N →₀ ℕ) → (Fin (D + 2) →₀ ℕ) := fun s =>
    Finsupp.equivFunOnFinite.symm (fun i => s (Sum.inr i))
  let fu : (UXVar D N →₀ ℕ) → (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ) := fun s =>
    Finsupp.equivFunOnFinite.symm (fun o => Option.elim o (n' - uDeg s) (fun p => s (Sum.inl p)))
  have hmaps : ∀ s ∈ Q.support, (fun s => (fx s, fu s)) s ∈
      (Finset.univ.finsuppAntidiag n) ×ˢ (Finset.univ.finsuppAntidiag n') := by
    intro s hs
    simp only [Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
    constructor
    · simpa [fx, xDeg] using hx s hs
    · have := hu s hs
      simp only [fu, Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_option, Option.elim]
      unfold uDeg at this ⊢
      omega
  have hinj : Set.InjOn (fun s => (fx s, fu s)) Q.support := by
    intro s _ t _ hst
    simp only [Prod.mk.injEq] at hst
    ext v
    rcases v with p | i
    · have := congrArg (fun f => f (some p)) hst.2
      simpa [fu] using this
    · have := congrArg (fun f => f i) hst.1
      simpa [fx] using this
  calc Q.support.card ≤ ((Finset.univ.finsuppAntidiag n) ×ˢ (Finset.univ.finsuppAntidiag n')).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = _ := by
      rw [Finset.card_product, Finset.card_finsuppAntidiag_nat_eq_choose,
        Finset.card_finsuppAntidiag_nat_eq_choose]
      simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_option, Fintype.card_prod]
      congr 1
      · rw [show D + 2 + n - 1 = n + D + 1 by omega]
        exact Nat.choose_symm_of_eq_add (by omega)
      · rw [show (D + 2) * (N + 1) + 1 + n' - 1 = n' + (D + 2) * (N + 1) by omega]
        exact Nat.choose_symm_of_eq_add (by omega)

noncomputable def Ey {D N : ℕ} (y : Fin (N + 1) → ℂ) :
    MvPolynomial (UXVar D N) ℂ →ₐ[ℂ] MvPolynomial (Fin (D + 2) × Fin (N + 1)) ℂ :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))

theorem sum_le_sqrt_card_mul {α : Type*} (s : Finset α) (a : α → ℝ) :
    ∑ i ∈ s, a i ≤ Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := by
  calc ∑ i ∈ s, a i ≤ |∑ i ∈ s, a i| := le_abs_self _
    _ = Real.sqrt ((∑ i ∈ s, a i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (s.card * ∑ i ∈ s, a i ^ 2) := Real.sqrt_le_sqrt sq_sum_le_card_mul_sum_sq
    _ = Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := Real.sqrt_mul (Nat.cast_nonneg _) _

theorem coeff_Ey_le {D N n n' : ℕ} (R : MvPolynomial (UXVar D N) ℂ) (hx : XHom n R)
    (hu : UDegLE n' R) (y : Fin (N + 1) → ℂ) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    ‖coeff β (Ey y R)‖ ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 R *
      Real.sqrt ((n + D + 1).choose (D + 1) *
        (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) * (∑ j, ‖y j‖) ^ n := by
  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality _ (Ey y R)).2 β
  set z := ReciprocityTheory.MultiplicativeHeights.torusPoint θ with hzdef
  have hz : ∀ p, ‖z p‖ = 1 := by
    intro p
    simp only [hzdef, ReciprocityTheory.MultiplicativeHeights.torusPoint]
    rw [Complex.norm_exp]
    simp
  set Y := ∑ j, ‖y j‖ with hY
  set pt : UXVar D N → ℂ := fun v => eval z (Sum.elim X (fun i => ∑ j, X (i, j) * C (y j)) v)
    with hpt
  have hev : eval z (Ey y R) = eval pt R := by
    have := congrArg (fun φ => φ R)
      (MvPolynomial.comp_aeval (R := ℂ) (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))
        (aeval z))
    simp only [AlgHom.comp_apply] at this
    calc eval z (Ey y R) = aeval z (Ey y R) := by simp
      _ = _ := this
      _ = eval pt R := by simp [hpt]
  have hpt1 : ∀ p, ‖pt (Sum.inl p)‖ = 1 := fun p => by simp [hpt, hz]
  have hpt2 : ∀ i, ‖pt (Sum.inr i)‖ ≤ Y := by
    intro i
    simp only [hpt, Sum.elim_inr, map_sum, map_mul, eval_X, eval_C]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, hz, one_mul]
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmono : ∀ α ∈ R.support, ‖∏ v, pt v ^ α v‖ ≤ Y ^ n := by
    intro α hα
    rw [norm_prod, Fintype.prod_sum_type]
    simp only [norm_pow, hpt1, one_pow, Finset.prod_const_one, one_mul]
    calc ∏ i, ‖pt (Sum.inr i)‖ ^ α (Sum.inr i) ≤ ∏ i, Y ^ α (Sum.inr i) :=
          Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpt2 i) _
      _ = Y ^ n := by rw [Finset.prod_pow_eq_pow_sum, ← hx α hα]; rfl
  have hcard := card_support_le R hx hu
  calc ‖coeff β (Ey y R)‖ ≤ ‖eval z (Ey y R)‖ := hθ
    _ = ‖∑ α ∈ R.support, coeff α R * ∏ v, pt v ^ α v‖ := by rw [hev, eval_eq']
    _ ≤ ∑ α ∈ R.support, ‖coeff α R‖ * Y ^ n := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmono α hα) (norm_nonneg _)
    _ = (∑ α ∈ R.support, ‖coeff α R‖) * Y ^ n := by rw [Finset.sum_mul]
    _ ≤ (Real.sqrt R.support.card * ReciprocityTheory.MultiplicativeHeights.polyL2 R) * Y ^ n := by
        gcongr
        exact sum_le_sqrt_card_mul _ _
    _ ≤ _ := by
        rw [mul_comm (Real.sqrt _) (ReciprocityTheory.MultiplicativeHeights.polyL2 R)]
        gcongr
        unfold ReciprocityTheory.MultiplicativeHeights.polyL2; positivity

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}

noncomputable def evW (w : Fin (N + 1) → B) :
    MvPolynomial (UXVar D N) R →ₐ[R] MvPolynomial (Fin (D + 2) × Fin (N + 1)) B :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (w j))

def CoeffIn (W : Submodule R B) (m : ℕ) (p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) : Prop :=
  ∀ β, coeff β p ∈ W ^ m

variable (W : Submodule R B)


theorem coeffIn_mul {m m' : ℕ} {p q : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (hq : CoeffIn W m' q) : CoeffIn W (m + m') (p * q) := fun β => by
  rw [coeff_mul, pow_add]
  exact Submodule.sum_mem _ fun x _ => Submodule.mul_mem_mul (hp _) (hq _)

theorem coeffIn_one : CoeffIn W 0 (1 : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [pow_zero, coeff_one]
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _

theorem coeffIn_pow {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (k : ℕ) : CoeffIn W (m * k) (p ^ k) := by
  induction k with
  | zero => simpa using coeffIn_one W
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact coeffIn_mul W ih hp

theorem coeffIn_prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin (D + 2) × Fin (N + 1)) B)
    (m : ι → ℕ) (h : ∀ i ∈ s, CoeffIn W (m i) (p i)) : CoeffIn W (∑ i ∈ s, m i) (∏ i ∈ s, p i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using coeffIn_one W) ?_
  intro a s ha ih h
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact coeffIn_mul W (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem coeffIn_smul {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (r : R) : CoeffIn W m (C (algebraMap R B r) * p) := fun β => by
  rw [coeff_C_mul, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hp β)

theorem coeffIn_X (u : Fin (D + 2) × Fin (N + 1)) : CoeffIn W 0 (X u : MvPolynomial _ B) := fun β => by
  rw [pow_zero, coeff_X']
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _

theorem coeffIn_lin (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) (i : Fin (D + 2)) :
    CoeffIn W 1 (∑ j, X (i, j) * C (w j) : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [coeff_sum, pow_one]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [mul_comm, coeff_C_mul, coeff_X']
  split_ifs
  · rw [mul_one]
    exact hw j
  · rw [mul_zero]
    exact zero_mem _

private theorem sum_support_inr_eq_xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) :
    ∑ x ∈ s.support, Sum.elim (fun _ => 0) (fun i => s (Sum.inr i)) x = xDeg s := by
  rw [xDeg, Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]
  · simp
  · intro x _ hx
    cases x with
    | inl p => rfl
    | inr i => simpa using hx

theorem coeffIn_evW (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) {n : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) : CoeffIn W n (evW w Q) := by
  intro β
  rw [Q.as_sum, map_sum, coeff_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hterm : CoeffIn W n (evW w (monomial s (coeff s Q))) := by
    rw [evW, aeval_monomial, MvPolynomial.algebraMap_apply]
    apply coeffIn_smul
    rw [Finsupp.prod, ← hx s hs, ← sum_support_inr_eq_xDeg s]
    refine coeffIn_prod W s.support _ _ fun x _ => ?_
    cases x with
    | inl p => simpa using coeffIn_pow W (coeffIn_X W p) (s (Sum.inl p))
    | inr i => simpa using coeffIn_pow W (coeffIn_lin W w hw i) (s (Sum.inr i))
  exact hterm β

theorem coeff_evW_mem (w : Fin (N + 1) → B) {n : ℕ} (Q : MvPolynomial (UXVar D N) R)
    (hx : XHom n Q) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    coeff β (evW w Q) ∈
      Submodule.span R (Set.range fun s : Fin n → Fin (N + 1) => ∏ k, w (s k)) := by
  have h := coeffIn_evW (Submodule.span R (Set.range w)) w (fun j => Submodule.subset_span ⟨j, rfl⟩) Q hx β
  rw [Submodule.span_pow] at h
  refine Submodule.span_mono ?_ h
  intro a ha
  rw [Set.mem_pow] at ha
  obtain ⟨f, rfl⟩ := ha
  choose s hs using fun k => (f k).2
  refine ⟨s, ?_⟩
  show ∏ k, w (s k) = _
  rw [List.prod_ofFn]
  exact Finset.prod_congr rfl fun k _ => hs k

end

theorem evW_factor {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B] [Algebra S B] [IsScalarTower R S B] {D N n : ℕ} (y : Fin (N + 1) → S) (w0 : B)
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) :
    evW (fun j => algebraMap S B (y j) * w0) Q =
      MvPolynomial.map (algebraMap S B) (evW y Q) * C (w0 ^ n) := by
  rw [Q.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [evW, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul, map_C, Finsupp.prod,
    map_prod, map_pow]
  rw [← IsScalarTower.algebraMap_apply, mul_assoc]
  congr 1
  rw [← hx s hs, ← sum_support_inr_eq_xDeg s]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  cases x with
  | inl p => simp
  | inr i =>
    simp only [Sum.elim_inr, map_sum, map_mul, map_X, map_C]
    rw [← mul_pow, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem map_evW_eq {K S : Type*} [Field K] [CommRing S] [Algebra K S] {D N : ℕ} (P : S →+* ℂ)
    (sg : K →+* ℂ) (hP : P.comp (algebraMap K S) = sg) (y : Fin (N + 1) → S)
    (R : MvPolynomial (UXVar D N) K) :
    MvPolynomial.map P (evW (R := K) y R) = Ey (fun j => P (y j)) (MvPolynomial.map sg R) := by
  have h : (MvPolynomial.map P).comp (evW (R := K) (D := D) y).toRingHom =
      (Ey (D := D) (fun j => P (y j))).toRingHom.comp (MvPolynomial.map sg) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evW, Ey, ← hP]
    · intro i
      cases i <;> simp [evW, Ey]
  exact RingHom.congr_fun h R

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

def cardUX (D N n n' : ℕ) : ℕ :=
  (n + D + 1).choose (D + 1) * (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1))

noncomputable def qnorm {D N : ℕ} (σ : K →+* ℂ) (F1 : MvPolynomial (UXVar D N) K) (n n' : ℕ)
    (Q : MvPolynomial (UXVar D N) (𝓞 K)) : ℝ :=
  ⨅ P : {P : MvPolynomial (UXVar D N) ℂ //
      XHom n (MvPolynomial.map σ F1 * P) ∧ UDegLE n' (MvPolynomial.map σ F1 * P)},
    ReciprocityTheory.MultiplicativeHeights.polyL2 (MvPolynomial.map (σ.comp (algebraMap (𝓞 K) K)) Q +
      MvPolynomial.map σ F1 * P.1)

noncomputable abbrev mapK {D N : ℕ} (Q : MvPolynomial (UXVar D N) (𝓞 K)) :
    MvPolynomial (UXVar D N) K :=
  MvPolynomial.map (algebraMap (𝓞 K) K) Q

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def n96' : ℕ := 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del

theorem evc_eq (c : ι) : d.evc c = evW (R := K) (D := d.D) (fun j => d.w j c) := by
  unfold Data.evc evW
  congr 1
  funext v
  cases v <;> rfl

theorem w_eq_smul (hd : d.AxH 𝒜) (c : ι) (j : Fin (d.N + 1)) :
    d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hex : ∃ a : Ω c, d.w j c = a • d.w (d.jc c) c := by
    have h1 := hd.finrank_one c d.wL
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨d.w (d.jc c) c, hd.w_mem _ _⟩ : 𝒜 c d.wL)
      (fun h => hd.w_base c (congrArg Subtype.val h))).mp h1 ⟨d.w j c, hd.w_mem _ _⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  unfold ratio
  rw [dif_pos hex]
  exact hex.choose_spec

theorem lineSection_pow_mem (hd : d.AxH 𝒜) (c : ι) (k : ℕ) : d.w (d.jc c) c ^ k ∈ 𝒜 c (k • d.wL) := by
  haveI := hd.graded c
  exact SetLike.pow_mem_graded k (hd.w_mem (d.jc c) c)

theorem lineSection_pow_ne (hd : d.AxH 𝒜) (c : ι) (k : ℕ) : d.w (d.jc c) c ^ k ≠ 0 := by
  induction k with
  | zero =>
    haveI : Nontrivial (A c) := nontrivial_of_ne _ _ (hd.w_base c)
    rw [pow_zero]
    exact one_ne_zero
  | succ k ih =>
    rw [pow_succ]
    exact hd.mul_ne_zero c (lineSection_pow_mem d hd c k) (hd.w_mem _ _) ih (hd.w_base c)

theorem norm_lineSection_pow (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) (k : ℕ) (hk : 1 ≤ k) :
    d.nrm c (k • d.wL) (d.w (d.jc c) c ^ k) P = d.nrm c d.wL (d.w (d.jc c) c) P ^ k := by
  induction k, hk using Nat.le_induction with
  | base => rw [one_smul, pow_one, pow_one]
  | succ k hk ih =>
    rw [succ_nsmul, pow_succ, pow_succ, hd.nrm_mul c P (lineSection_pow_mem d hd c k) (hd.w_mem _ _)
      (lineSection_pow_ne d hd c k) (hd.w_base c), ih]

theorem map_evW_global (hd : d.AxH 𝒜) (c : ι) (Q : MvPolynomial (UXVar d.D d.N) (𝓞 K)) :
    MvPolynomial.map (Pi.evalRingHom A c) (evW (R := 𝓞 K) (D := d.D) d.w Q) = d.evc c (mapK Q) := by
  haveI := hd.towerO c
  have key : (MvPolynomial.map (Pi.evalRingHom A c)).comp
      (evW (R := 𝓞 K) (D := d.D) d.w).toRingHom =
      (d.evc c).toRingHom.comp (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evW, Data.evc,
        MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_apply]
      congr 1
    · intro v
      cases v <;> simp [evW, Data.evc]
  exact RingHom.congr_fun key Q

theorem meanK_mono {f g : (K →+* ℂ) → ℝ} (h : ∀ sg, f sg ≤ g sg) : meanK f ≤ meanK g := by
  unfold meanK
  gcongr with sg
  exact h sg

theorem meanK_affine (a b : (K →+* ℂ) → ℝ) (u v e : ℝ) :
    meanK (fun sg => a sg + u + v * (b sg + e)) = meanK a + u + v * (meanK b + e) := by
  unfold meanK
  have hn : (Fintype.card (K →+* ℂ) : ℝ) ≠ 0 := by
    rw [NumberField.Embeddings.card]
    exact_mod_cast (Module.finrank_pos).ne'
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  field_simp

theorem up_cauchy (hd : d.AxH 𝒜) (hdel : 1 ≤ d.del) (c : ι) (F1 : MvPolynomial (UXVar d.D d.N) K)
    (deF : ℕ) (hxF : XHom deF F1)
    (hker : ∀ (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K), XHom n Q → (d.evc c Q = 0 ↔ F1 ∣ Q))
    (Q : MvPolynomial (UXVar d.D d.N) (𝓞 K)) (hQx : XHom d.n96 (mapK Q))
    (hQu : UDegLE d.n96' (mapK Q)) (hQ : ¬ F1 ∣ mapK Q) :
    ∃ g ∈ Submodule.span (𝓞 K)
        (Set.range fun s : Fin d.n96 → Fin (d.N + 1) => ∏ k, d.w (s k)), g c ≠ 0 ∧
      meanK (fun sg => Real.log (d.supNc c sg (d.n96 • d.wL) (g c))) ≤
        meanK (fun σ => Real.log (qnorm σ F1 d.n96 d.n96' Q)) +
          1 / 2 * Real.log (cardUX d.D d.N d.n96 d.n96') +
          d.n96 * (d.laW + Real.log (d.N + 1 : ℕ)) := by
  classical
  have := hd.tower c
  have := hd.towerO c
  have hn1 : 1 ≤ d.n96 := by
    unfold n96
    have : 0 < d.N + 1 := Nat.succ_pos _
    have : 0 < (d.D + 2) * (d.N + 1) := by positivity
    have : 0 < 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊) := by positivity
    omega
  set n := d.n96 with hn
  set n' := d.n96' with hn'
  set w0 := d.w (d.jc c) c with hw0
  set y : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) w0 with hy
  have hwy : (fun j => d.w j c) = fun j => algebraMap (Ω c) (A c) (y j) * w0 :=
    funext fun j => by rw [← Algebra.smul_def]; exact d.w_eq_smul hd c j
  have hfac : ∀ (m : ℕ) (R : MvPolynomial (UXVar d.D d.N) K), XHom m R →
      d.evc c R = MvPolynomial.map (algebraMap (Ω c) (A c)) (evW (R := K) y R) *
        MvPolynomial.C (w0 ^ m) := by
    intro m R hR
    rw [d.evc_eq, hwy]
    exact evW_factor y w0 R hR
  have hcoef : ∀ (m : ℕ) (R : MvPolynomial (UXVar d.D d.N) K), XHom m R → ∀ β,
      MvPolynomial.coeff β (d.evc c R) = MvPolynomial.coeff β (evW (R := K) y R) • w0 ^ m := by
    intro m R hR β
    rw [hfac m R hR, mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      Algebra.smul_def, mul_comm]

  have hF1 : evW (R := K) y F1 = 0 := by
    have h0 : d.evc c F1 = 0 := (hker deF F1 hxF).mpr dvd_rfl
    ext β
    have := hcoef deF F1 hxF β
    rw [h0, MvPolynomial.coeff_zero] at this
    rw [MvPolynomial.coeff_zero]
    exact (smul_eq_zero.mp this.symm).resolve_right (d.lineSection_pow_ne hd c deF)

  have hQk : d.evc c (mapK Q) ≠ 0 := fun h => hQ ((hker n _ hQx).mp h)
  obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hQk
  have hQxO : XHom n Q := by
    intro s hs
    apply hQx s
    rwa [mapK, MvPolynomial.support_map_of_injective _ (IsFractionRing.injective (𝓞 K) K)]
  set g := MvPolynomial.coeff β (evW (R := 𝓞 K) (D := d.D) d.w Q) with hgdef
  have hgc : g c = MvPolynomial.coeff β (d.evc c (mapK Q)) := by
    rw [← d.map_evW_global hd c Q, MvPolynomial.coeff_map]; rfl
  set φ := MvPolynomial.coeff β (evW (R := K) y (mapK Q)) with hφdef
  have hgφ : g c = φ • w0 ^ n := by rw [hgc, hcoef n _ hQx β]
  have hgne : g c ≠ 0 := by rw [hgc]; exact hβ
  have hφ : φ ≠ 0 := by rintro h; apply hgne; rw [hgφ, h, zero_smul]
  have hgmem : g c ∈ 𝒜 c (n • d.wL) := by rw [hgφ]; exact Submodule.smul_mem _ φ (d.lineSection_pow_mem hd c n)
  refine ⟨g, by convert coeff_evW_mem d.w Q hQxO β <;> first | rfl | exact Module.ext' _ _ (fun r m => funext fun i => by haveI := hd.towerO i; simp only [Algebra.smul_def, Pi.smul_apply, Pi.mul_apply]; rw [IsScalarTower.algebraMap_apply (𝓞 K) K (A i) r]; rfl), hgne, ?_⟩

  set S : (K →+* ℂ) → ℝ := fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j)) with hS
  have hcardpos : (0 : ℝ) < cardUX d.D d.N n n' := by
    unfold cardUX
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  set Cst : (K →+* ℂ) → ℝ := fun sg =>
    Real.sqrt (cardUX d.D d.N n n') * (((d.N + 1 : ℕ) : ℝ) * Real.exp (S sg)) ^ n with hCst
  have hCpos : ∀ sg, 0 < Cst sg := fun sg => by
    simp only [hCst]
    have : (0 : ℝ) < ((d.N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have := Real.sqrt_pos.mpr hcardpos
    positivity
  have hbound : ∀ (sg : K →+* ℂ) (P : PT (Ω := Ω c) sg),
      d.nrm c (n • d.wL) (g c) P ≤ qnorm sg F1 n n' Q * Cst sg := by
    intro sg P
    have hP : (P : Ω c →+* ℂ).comp (algebraMap K (Ω c)) = sg := P.2

    have hwj : ∀ j, ‖(P : Ω c →+* ℂ) (y j)‖ * d.nrm c d.wL w0 P ≤ Real.exp (S sg) := by
      intro j
      have hle : ‖(P : Ω c →+* ℂ) (y j)‖ * d.nrm c d.wL w0 P = d.nrm c d.wL (d.w j c) P := by
        by_cases hyj : y j = 0
        · have : d.w j c = 0 := by rw [d.w_eq_smul hd c j]; simp only [hy] at hyj; rw [hyj, zero_smul]
          rw [this, hd.nrm_zero, hyj, map_zero, norm_zero, zero_mul]
        · conv_rhs => rw [d.w_eq_smul hd c j]
          rw [hd.nrm_smul c P (y j) (hd.w_mem _ c) (hd.w_base c) hyj]
      rw [hle]
      have hmemW : d.w j ∈ d.WW := by rw [hd.WW_span]; exact Submodule.subset_span ⟨j, rfl⟩
      have hb := hd.bdd sg d.wL (d.w j) (Or.inl ⟨hmemW, rfl⟩)
      have h1 : d.nrm c d.wL (d.w j c) P ≤ d.supN sg d.wL (d.w j) :=
        le_ciSup hb (⟨c, P⟩ : Σ c, PT (Ω := Ω c) sg)
      by_cases hs : d.supN sg d.wL (d.w j) ≤ 0
      · exact h1.trans (hs.trans (Real.exp_pos _).le)
      · replace hs := not_le.mp hs
        refine h1.trans ?_
        rw [← Real.exp_log hs]
        exact Real.exp_le_exp.mpr
          (le_ciSup (f := fun j => Real.log (d.supN sg d.wL (d.w j))) (Finite.bddAbove_range _) j)
    have hnrm0 : 0 ≤ d.nrm c d.wL w0 P := (hd.nrm_pos c P (hd.w_mem _ c) (hd.w_base c)).le
    have hsum : (∑ j, ‖(P : Ω c →+* ℂ) (y j)‖) * d.nrm c d.wL w0 P ≤
        ((d.N + 1 : ℕ) : ℝ) * Real.exp (S sg) := by
      rw [Finset.sum_mul]
      calc ∑ j, ‖(P : Ω c →+* ℂ) (y j)‖ * d.nrm c d.wL w0 P ≤ ∑ _j : Fin (d.N + 1), Real.exp (S sg) :=
            Finset.sum_le_sum fun j _ => hwj j
        _ = _ := by simp

    have hval : d.nrm c (n • d.wL) (g c) P =
        ‖MvPolynomial.coeff β (Ey (D := d.D) (fun j => (P : Ω c →+* ℂ) (y j))
          (MvPolynomial.map sg (mapK Q)))‖ * d.nrm c d.wL w0 P ^ n := by
      rw [hgφ, hd.nrm_smul c P φ (d.lineSection_pow_mem hd c n) (d.lineSection_pow_ne hd c n) hφ,
        d.norm_lineSection_pow hd c P n hn1, ← map_evW_eq (P : Ω c →+* ℂ) sg hP, MvPolynomial.coeff_map]

    have hQ' : ∀ P' : {P' : MvPolynomial (UXVar d.D d.N) ℂ //
        XHom n (MvPolynomial.map sg F1 * P') ∧ UDegLE n' (MvPolynomial.map sg F1 * P')},
        d.nrm c (n • d.wL) (g c) P / Cst sg ≤
          ReciprocityTheory.MultiplicativeHeights.polyL2 (MvPolynomial.map (sg.comp (algebraMap (𝓞 K) K)) Q +
            MvPolynomial.map sg F1 * P'.1) := by
      intro P'
      set R := MvPolynomial.map (sg.comp (algebraMap (𝓞 K) K)) Q + MvPolynomial.map sg F1 * P'.1
      have hRQ : MvPolynomial.map (sg.comp (algebraMap (𝓞 K) K)) Q = MvPolynomial.map sg (mapK Q) := by
        rw [mapK, MvPolynomial.map_map]
      have hRx : XHom n R := by
        intro s hs
        rcases Finset.mem_union.mp (MvPolynomial.support_add hs) with h | h
        · rw [hRQ] at h; exact hQx s (MvPolynomial.support_map_subset _ _ h)
        · exact P'.2.1 s h
      have hRu : UDegLE n' R := by
        intro s hs
        rcases Finset.mem_union.mp (MvPolynomial.support_add hs) with h | h
        · rw [hRQ] at h; exact hQu s (MvPolynomial.support_map_subset _ _ h)
        · exact P'.2.2 s h
      have hER : Ey (D := d.D) (fun j => (P : Ω c →+* ℂ) (y j)) R =
          Ey (D := d.D) (fun j => (P : Ω c →+* ℂ) (y j)) (MvPolynomial.map sg (mapK Q)) := by
        simp only [R, map_add, map_mul, hRQ, ← map_evW_eq (P : Ω c →+* ℂ) sg hP, hF1, map_zero,
          zero_mul, add_zero]
      have hC := coeff_Ey_le R hRx hRu (fun j => (P : Ω c →+* ℂ) (y j)) β
      rw [hER] at hC
      rw [div_le_iff₀ (hCpos sg), hval]
      simp only [hCst]
      have hL2 : 0 ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 R := by unfold ReciprocityTheory.MultiplicativeHeights.polyL2; positivity
      have hpow : (∑ j, ‖(P : Ω c →+* ℂ) (y j)‖) ^ n * d.nrm c d.wL w0 P ^ n ≤
          (((d.N + 1 : ℕ) : ℝ) * Real.exp (S sg)) ^ n := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsum n
      calc ‖MvPolynomial.coeff β _‖ * d.nrm c d.wL w0 P ^ n
          ≤ (ReciprocityTheory.MultiplicativeHeights.polyL2 R * Real.sqrt (cardUX d.D d.N n n') *
              (∑ j, ‖(P : Ω c →+* ℂ) (y j)‖) ^ n) * d.nrm c d.wL w0 P ^ n := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            simpa [cardUX] using hC
        _ = ReciprocityTheory.MultiplicativeHeights.polyL2 R * Real.sqrt (cardUX d.D d.N n n') *
              ((∑ j, ‖(P : Ω c →+* ℂ) (y j)‖) ^ n * d.nrm c d.wL w0 P ^ n) := by ring
        _ ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 R * Real.sqrt (cardUX d.D d.N n n') *
              (((d.N + 1 : ℕ) : ℝ) * Real.exp (S sg)) ^ n := by gcongr
        _ = _ := by ring
    have hne : Nonempty {P' : MvPolynomial (UXVar d.D d.N) ℂ //
        XHom n (MvPolynomial.map sg F1 * P') ∧ UDegLE n' (MvPolynomial.map sg F1 * P')} :=
      ⟨⟨0, by simp [XHom], by simp [UDegLE]⟩⟩
    have := le_ciInf hQ'
    rw [div_le_iff₀ (hCpos sg)] at this
    exact this

  have hsg : ∀ sg : K →+* ℂ, Real.log (d.supNc c sg (n • d.wL) (g c)) ≤
      Real.log (qnorm sg F1 n n' Q) + 1 / 2 * Real.log (cardUX d.D d.N n n') +
        n * (S sg + Real.log (d.N + 1 : ℕ)) := by
    intro sg
    obtain ⟨P0, hP0⟩ := exists_embedding_over (hd.fg c) sg
    haveI : Nonempty (PT (Ω := Ω c) sg) := ⟨⟨P0, hP0⟩⟩
    have hsup : d.supNc c sg (n • d.wL) (g c) ≤ qnorm sg F1 n n' Q * Cst sg :=
      ciSup_le fun P => hbound sg P
    have hpos0 : 0 < d.nrm c (n • d.wL) (g c) P0 := hd.nrm_pos c P0 hgmem hgne
    have hsuppos : 0 < d.supNc c sg (n • d.wL) (g c) :=
      hpos0.trans_le (le_ciSup ⟨qnorm sg F1 n n' Q * Cst sg, by
        rintro _ ⟨P, rfl⟩; exact hbound sg P⟩ (⟨P0, hP0⟩ : PT (Ω := Ω c) sg))
    have hqpos : 0 < qnorm sg F1 n n' Q := by
      by_contra hq
      replace hq := not_lt.mp hq
      have := mul_nonpos_of_nonpos_of_nonneg hq (hCpos sg).le
      linarith
    have hexp : 0 < Real.exp (S sg) := Real.exp_pos _
    have hN : (0 : ℝ) < ((d.N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    calc Real.log (d.supNc c sg (n • d.wL) (g c)) ≤ Real.log (qnorm sg F1 n n' Q * Cst sg) :=
          Real.log_le_log hsuppos hsup
      _ = _ := by
          simp only [hCst]
          rw [Real.log_mul hqpos.ne' (hCpos sg).ne', Real.log_mul (Real.sqrt_pos.mpr hcardpos).ne'
            (by positivity), Real.log_sqrt hcardpos.le, Real.log_pow, Real.log_mul hN.ne' hexp.ne',
            Real.log_exp]
          ring
  calc meanK (fun sg => Real.log (d.supNc c sg (n • d.wL) (g c)))
      ≤ meanK (fun sg => Real.log (qnorm sg F1 n n' Q) + 1 / 2 * Real.log (cardUX d.D d.N n n') +
          n * (S sg + Real.log (d.N + 1 : ℕ))) := meanK_mono hsg
    _ = _ := by rw [meanK_affine]; rfl

theorem log_le_half {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / 2 := by
  have hs := Real.sqrt_pos.mpr hy
  have h1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log y = 2 * Real.log (Real.sqrt y) := by
    rw [Real.log_sqrt hy.le]
    ring
  have h3 := Real.sq_sqrt hy.le
  nlinarith [sq_nonneg (Real.sqrt y - 2)]

theorem up_count (hd : d.AxH 𝒜) (hdel : 1 ≤ d.del) :
    Real.log (cardUX d.D d.N d.n96 d.n96') + d.PO ≤ d.n96 := by
  obtain ⟨M, hM⟩ : ∃ M, M = (d.D + 2) * (d.N + 1) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = 1 + ⌈d.PO⌉₊ := ⟨_, rfl⟩
  have hD := hd.D_ge
  have hM2 : d.D + 2 ≤ M := by rw [hM]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hn : d.n96 = 8 * M ^ 2 * (d.D + 1) * d.del * t := by rw [hM, ht]; rfl
  have hn' : d.n96' = 8 * d.n96 * M * (d.D + 1) * d.del := by rw [hM]; rfl
  have ht1 : 1 ≤ t := by omega
  have hM1 : 1 ≤ M := by omega
  have hnM : 32 * M ^ 2 * t ≤ d.n96 := by
    rw [hn]
    have : 32 * M ^ 2 * t ≤ 8 * M ^ 2 * 4 * 1 * t := by ring_nf; exact le_refl _
    calc 32 * M ^ 2 * t = 8 * M ^ 2 * 4 * 1 * t := by ring
      _ ≤ 8 * M ^ 2 * (d.D + 1) * d.del * t := by gcongr <;> omega
  have hnpos : 2 ≤ d.n96 := by nlinarith
  set n := d.n96 with hnn

  have hnn' : d.n96' * M ≤ n * n := by
    rw [hn']
    calc 8 * n * M * (d.D + 1) * d.del * M = n * (8 * M ^ 2 * (d.D + 1) * d.del) := by ring
      _ ≤ n * (8 * M ^ 2 * (d.D + 1) * d.del * t) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ ht1)
      _ = n * n := by rw [hn]
  have hA : n + d.D + 1 ≤ n ^ 2 := by nlinarith
  have hB : d.n96' + M ≤ n ^ 2 := by nlinarith
  have hcard : cardUX d.D d.N n d.n96' ≤ n ^ (4 * M) := by
    unfold cardUX
    rw [← hM]
    calc (n + d.D + 1).choose (d.D + 1) * (d.n96' + M).choose M
        ≤ (n ^ 2) ^ (d.D + 1) * (n ^ 2) ^ M :=
          Nat.mul_le_mul ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hA _))
            ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hB _))
      _ = n ^ (2 * (d.D + 1 + M)) := by ring
      _ ≤ n ^ (4 * M) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcpos : 0 < cardUX d.D d.N n d.n96' := by
    unfold cardUX
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hlog1 : Real.log (cardUX d.D d.N n d.n96') ≤ (4 * M : ℕ) * Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast hcpos) (by exact_mod_cast hcard)
  have hlogn : Real.log n ≤ n / (16 * M) + 3 * Real.log 2 + M / 2 := by
    have h8 : (0 : ℝ) < 8 * M := by positivity
    have e : (n : ℝ) = n / (8 * M) * (8 * M) := by field_simp
    rw [e, Real.log_mul (by positivity) h8.ne', Real.log_mul (by norm_num) (by positivity)]
    have : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [this]
    have a1 := log_le_half (show (0 : ℝ) < n / (8 * M) by positivity)
    have a2 := log_le_half (show (0 : ℝ) < M by positivity)
    have : (n : ℝ) / (8 * M) / 2 = n / (8 * M) * (8 * M) / (16 * M) := by field_simp; ring
    linarith
  have hl2 := Real.log_two_lt_d9
  have hPO : d.PO ≤ t := by
    have := Nat.le_ceil d.PO
    rw [ht]; push_cast; linarith
  have hnMR : 32 * (M : ℝ) ^ 2 * t ≤ n := by exact_mod_cast hnM
  have key : (4 * M : ℝ) * (n / (16 * M)) = n / 4 := by field_simp; ring
  have h4 : ((4 * M : ℕ) : ℝ) = 4 * M := by push_cast; ring
  rw [h4] at hlog1
  have : (4 * M : ℝ) * Real.log n ≤ n / 4 + 12 * M * Real.log 2 + 2 * M ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlogn (by positivity : (0 : ℝ) ≤ 4 * M)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left htR (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 2),
    mul_le_mul_of_nonneg_left hMR (by positivity : (0 : ℝ) ≤ (M : ℝ))]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
