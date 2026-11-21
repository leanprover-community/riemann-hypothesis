import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLintegralSqNeTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinBarOps

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

theorem linForm_eq {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem sum_transpose_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (g : Matrix m m K) (Y L : Matrix m n K) :
    ∑ k, ∑ j, (gᵀ * Y) k j * L k j = ∑ k, ∑ j, Y k j * (g * L) k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ x, ∑ i, ∑ j, g i x * Y i j * L x j := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ j, g i x * Y i j * L x j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ x, g i x * Y i j * L x j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.LinBarOps

namespace GlobalTheory.LinBarOps

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

theorem at_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem heis_ops : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) ∧ GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ ≠ 1 ∧
    ∃ (wT : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁))
      (wM : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
    ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l Y) * ι φ Y) ∧
      (∀ g C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ)) =
        fun Y => ι (S g φ) (Y + ((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * C)) ∧
      (∀ g l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l (g.valᵀ * Y)) * ι (S g φ) Y) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hT K hK S hSB h4
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  refine ⟨GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _, GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _, ?_⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : Γ.V'.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w)
    have e : (Γ.V'.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : Γ.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w)
    have e : (Γ.W.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := Γ.W.J.map Bs.τ₁ with hBdef
  have hA : IsUnit A.det := by
    have e : A.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdV ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hB : IsUnit Bᵀ.det := by
    have e : B.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hBm : IsUnit B.det := by rw [← Matrix.det_transpose]; exact hB
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm Bs.v₁ Bs.τ₁ P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) :=
    fun C => -(A⁻¹ * C * (Bᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) →
      Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (Bs.τ₁.comp σ)) * Bᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F Bs.v₁) x → x.map (piW Bs.τ₁) = 0 →
      u.map (piW (Bs.τ₁.comp σ)) = 0 →
      Bs.ψ (symp (R := AF F) (cA σ) (-1) (incM F Γ.V'.J) (incM F Γ.W.J) x u) =
        GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁
          (-(∑ k, ∑ j, (-(A * x.map (piW (Bs.τ₁.comp σ)) * Bᵀ)) k j * u.map (piW Bs.τ₁) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm Bs.v₁ Bs.τ₁ _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm Bs.τ₁ Γ.V'.J Γ.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]
    rfl
  refine ⟨fun C => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U 0 (Pm C)),
    fun l => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U (-Lm l) 0), ?_⟩
  intro ι hι
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hK' : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      actAB (cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) u = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u := by
    intro g u
    simp [actAB, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]
  have hKat : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F Bs.v₁) u →
      At (evFin F Bs.v₁) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u) := by
    intro g u hu r hr
    rw [← Matrix.mul_smul, hu r hr, Matrix.mul_zero]
  have hKmap : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (t : E →ₐ[F] Fv F Bs.v₁),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u).map (piW t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (piW t) * u.map (piW t) :=
    fun g u t => Matrix.map_mul
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) => GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB _) => GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hstd.1 Bs.v₁ w φ hφ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C φ hφ
    funext Y
    rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
  · intro l φ hφ
    funext Y
    have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
      (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, linForm_eq l Y]
    congr 2
    simp [Lm, Finset.sum_neg_distrib]
  · intro g C φ hφ
    funext Y
    rw [h4 g _ (hUat 0 (Pm C)) φ hφ, hK']
    have hat := hKat g _ (hUat 0 (Pm C))
    rw [htr _ hat (by rw [hKmap, hU0, Matrix.mul_zero]) _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) Y]
    congr 2
    rw [hKmap, (hK g).2.2, hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  · intro g l φ hφ
    funext Y
    rw [h4 g _ (hUat (-Lm l) 0) φ hφ, hK']
    have hat := hKat g _ (hUat (-Lm l) 0)
    have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * U (-Lm l) 0).map (piW (Bs.τ₁.comp σ)) = 0 := by
      rw [hKmap, hU1, Matrix.mul_zero]
    have hm := hmu _ hat h1 _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hKmap, (hK g).2.1, hU0, linForm_eq l]
    congr 2
    rw [show (∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * l (Matrix.single k j 1)) =
      ∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * Lm l k j from rfl, sum_transpose_mul]
    simp [Matrix.mul_neg, Finset.sum_neg_distrib]

end GlobalTheory.LinBarOps
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_heisenbergOperators_translation_char : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) ∧ GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ ≠ 1 ∧
    ∃ (wT : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁))
      (wM : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
    ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l Y) * ι φ Y) ∧
      (∀ g C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ)) =
        fun Y => ι (S g φ) (Y + ((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * C)) ∧
      (∀ g l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l (g.valᵀ * Y)) * ι (S g φ) Y) := by
  first | exact @GlobalTheory.LinBarOps.heis_ops | exact GlobalTheory.LinBarOps.heis_ops | (intros; apply GlobalTheory.LinBarOps.heis_ops <;> assumption)
end

section
open MeasureTheory Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  first | exact @GlobalTheory.ghom_factors_through_det | exact GlobalTheory.ghom_factors_through_det | (intros; apply GlobalTheory.ghom_factors_through_det <;> assumption)
end

section
section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_mem_integer_iff_of_valuation_eq_one {u : kˣ} (hu : valuation k (u : k) = 1) (y : k) :
    (u : k) * y ∈ 𝒪[k] ↔ y ∈ 𝒪[k] := by
  simp only [Valuation.mem_integer_iff, map_mul, hu, one_mul]

theorem intInd_diagAt_mul {n d : ℕ} {u : kˣ} (hu : valuation k (u : k) = 1) (i0 : Fin n)
    (Y : Matrix (Fin n) (Fin d) k) : intInd k n d ((diagAt u i0).valᵀ * Y) = intInd k n d Y := by
  have e : ∀ i j, ((diagAt u i0).valᵀ * Y) i j ∈ 𝒪[k] ↔ Y i j ∈ 𝒪[k] := by
    intro i j
    rw [diagAt_val, diagonal_transpose, diagonal_mul]
    by_cases hi : i = i0
    · rw [if_pos hi]; exact mul_mem_integer_iff_of_valuation_eq_one hu _
    · rw [if_neg hi, one_mul]
  have hs : ((diagAt u i0).valᵀ * Y) ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} ↔
      Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := by
    simp only [Set.mem_setOf_eq]
    exact forall_congr' fun i => forall_congr' fun j => e i j
  unfold intInd
  by_cases h : Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hs.mpr h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hs.mp h)]

theorem norm_char_unit_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤) →
    ∀ (_i0 : Fin n) (u : kˣ), valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1 := by
  intro k _ _ _ _ n d ι hinj S hS hiso χ hι φ0 hφ0 hι0 hfin i0 u hu
  set g := diagAt u i0 with hg
  have hmem : (χ u : ℂ) • φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.smul_mem _ _ hφ0
  have heq : S g φ0 = (χ u : ℂ) • φ0 := by
    refine hinj (hS g φ0 hφ0) hmem ?_
    rw [hι g φ0 hφ0, map_smul, hι0, det_diagAt]
    funext Y
    rw [intInd_diagAt_mul hu i0 Y]
    rfl
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  have hμ : Measure.IsAddHaarMeasure (Measure.addHaar : Measure (Fin n × Fin d → k)) := inferInstance
  have h := hiso g φ0 hφ0 Measure.addHaar hμ
  rw [heq] at h
  exact GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq h (hfin _ hμ).1 (hfin _ hμ).2

end GlobalTheory.HeisUnit
end
end

open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_character_unit_eq_one_heisenberg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤) →
    ∀ (_i0 : Fin n) (u : kˣ), valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1 := by
  atlas_forward_decl GlobalTheory.HeisUnit.norm_char_unit_eq_one
end

section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharSep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := (SplitWeil.isCompact_int k).exists_bound_of_continuousOn
    (f := fun y => ψ0 (x * y)) (hc.comp (continuous_const.mul continuous_id)).continuousOn
  have hpow : ∀ m : ℕ, ‖ψ0 x‖ ^ m ≤ B := fun m => by
    have hm : ((m : k)) ∈ 𝒪[k] := by
      simpa using (Subring.natCast_mem (𝒪[k]) m)
    have := hB _ hm
    rwa [show x * (m : k) = m • x by rw [nsmul_eq_mul, mul_comm], AddChar.map_nsmul_eq_pow, norm_pow] at this
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop B |>.exists
  exact absurd (hpow m) (not_le.mpr hm)

theorem norm_eq_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ = 1 := by
  have h1 := norm_le_one ψ0 hc x
  have h2 := norm_le_one ψ0 hc (-x)
  have hm : ψ0 x * ψ0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 x‖ * ‖ψ0 (-x)‖ = 1 := by rw [← norm_mul, hm, norm_one]
  by_contra hne
  have hlt : ‖ψ0 x‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖ψ0 x‖ * ‖ψ0 (-x)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
  linarith

def toCircle (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (h x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (show ψ0 (a + b) = ψ0 a * ψ0 b from AddChar.map_add_eq_mul ψ0 a b)

theorem toCircle_apply (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) (x : k) :
    ((toCircle ψ0 h x : Circle) : ℂ) = ψ0 x := rfl

theorem unitary_and_separates : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1 := by
  intro k _ _ _ _ ψ0 hc h1
  have hu := norm_eq_one ψ0 hc
  refine ⟨hu, fun a ha => ?_⟩
  set ψ := toCircle ψ0 hu
  have hψc : Continuous ψ := Continuous.subtype_mk hc _
  have hψ1 : ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [ψ, toCircle_apply] using this
  obtain ⟨c₀, hc₀⟩ := SplitWeil.exists_hasConductor_of_continuous ψ hψc hψ1
  have hx : a ∉ SplitWeil.cball (c₀ * c₀⁻¹) := by
    rw [mul_inv_cancel]
    intro h
    exact ha ((Valuation.mem_integer_iff _ _).mpr (by simpa [SplitWeil.cball] using h))
  obtain ⟨t, ht, hne⟩ := hc₀.exists_ne_one c₀ hx
  refine ⟨t, fun y hy => ?_, fun h => hne (Circle.ext (by simpa [ψ, toCircle_apply] using h))⟩
  have hy' : valuation k y ≤ 1 := hy
  have : t * y ∈ SplitWeil.cball c₀ := by
    simp only [SplitWeil.cball, Set.mem_setOf_eq, map_mul] at ht ⊢
    exact (mul_le_mul' le_rfl hy').trans (by rw [mul_one]; exact ht)
  have := hc₀.eq_one this
  simpa [ψ, toCircle_apply] using congrArg (fun z : Circle => (z : ℂ)) this

end GlobalTheory.CharSep
end
end

section
section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def entryForm (c : k) (i0 : Fin n) (j : Fin d) : Matrix (Fin n) (Fin d) k →ₗ[k] k where
  toFun Y := c * Y i0 j
  map_add' Y Y' := by simp [mul_add]
  map_smul' a Y := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mu_tr_eq_smul (ψ0 : AddChar k ℂ)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd k n d)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k)
    (hl : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i j, Y i j ∈ 𝒪[k]) → ψ0 (l Y) = 1)
    (C : Matrix (Fin n) (Fin d) k) :
    Mu l (Tr C φ0) = ψ0 (l (-C)) • Tr C φ0 := by
  obtain ⟨hT, hTι⟩ := hTr C φ0 hφ0
  obtain ⟨hM, hMι⟩ := hMu l _ hT
  refine hι hM ((GlobalTheory.WeilM.SB _).smul_mem _ hT) ?_
  rw [map_smul, hMι, hTι, hι0]
  funext Y
  simp only [Pi.smul_apply, smul_eq_mul, intInd]
  by_cases h : ∀ i j, (Y + C) i j ∈ 𝒪[k]
  · have e : ψ0 (l Y) = ψ0 (l (-C)) := by
      calc ψ0 (l Y) = ψ0 (l (Y + C) + l (-C)) := by rw [← map_add]; congr 2; abel
        _ = ψ0 (l (-C)) := by rw [AddChar.map_add_eq_mul, hl _ h, one_mul]
    rw [e]
  · rw [Set.indicator_of_notMem (show Y + C ∉ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} from h)]
    simp

theorem inner_eq_mul_inner (ψ0 : AddChar k ℂ)
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k) (f f' : (Fin n × Fin d → k) → ℂ)
    (hf : f ∈ GlobalTheory.WeilM.SB _) (hf' : f' ∈ GlobalTheory.WeilM.SB _) (a b : ℂ) (ha : Mu l f = a • f) (hb : Mu l f' = b • f') :
    ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ = a * (starRingEnd ℂ) b * ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ := by
  rw [← integral_const_mul, ← hMuI μ hμ l f hf f' hf', ha, hb]
  congr 1; funext y
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

end GlobalTheory.HeisUnit

namespace GlobalTheory.HeisUnit

theorem cosetRep_sub_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T T' : Fin d → SplitFlip.Res k 1) (j : Fin d) :
    (cosetRep ϖ i0 T' - cosetRep ϖ i0 T) i0 j =
      (ϖ : k)⁻¹ * (((Quotient.out (T j) : 𝒪[k]) : k) - ((Quotient.out (T' j) : 𝒪[k]) : k)) := by
  simp [cosetRep]; ring

theorem not_mem_int_of_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : SplitFlip.IsUnif ϖ) (t t' : SplitFlip.Res k 1) (h : t ≠ t') :
    (ϖ : k)⁻¹ * (((Quotient.out t : 𝒪[k]) : k) - ((Quotient.out t' : 𝒪[k]) : k)) ∉ 𝒪[k] := by
  intro ha
  apply h
  rw [← Ideal.Quotient.mk_out t, ← Ideal.Quotient.mk_out t', Ideal.Quotient.eq]
  have hs : Quotient.out t - Quotient.out t' ∈ Ideal.span {(⟨ϖ, hϖ.mem⟩ : 𝒪[k])} := by
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, ha⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub]
    field_simp
  convert hs using 1
  exact (pow_one _).trans hϖ.maximalIdeal_eq

theorem orth_of_charsep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ)
    (hcs : (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd k n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res k 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hTT
  set C := cosetRep ϖ i0 T
  set C' := cosetRep ϖ i0 T'
  have hna := not_mem_int_of_ne ϖ hϖ (T j) (T' j) hj
  rw [← cosetRep_sub_apply ϖ i0 T T' j] at hna
  obtain ⟨c, hc1, hc2⟩ := hcs.2 _ hna
  have hl : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i j, Y i j ∈ 𝒪[k]) → ψ0 (entryForm c i0 j Y) = 1 :=
    fun Y hY => hc1 _ (hY i0 j)
  have e1 := mu_tr_eq_smul ψ0 ι hι Tr hTr Mu hMu φ0 hφ0 hι0 _ hl C
  have e2 := mu_tr_eq_smul ψ0 ι hι Tr hTr Mu hMu φ0 hφ0 hι0 _ hl C'
  have hI := inner_eq_mul_inner ψ0 Mu hMuI μ hμ (entryForm c i0 j) _ _ (hTr C φ0 hφ0).1 (hTr C' φ0 hφ0).1 _ _ e1 e2
  have hA : ψ0 (entryForm c i0 j (-C)) * (starRingEnd ℂ) (ψ0 (entryForm c i0 j (-C'))) ≠ 1 := by
    rw [← Complex.inv_eq_conj (hcs.1 _), ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, ← map_neg, ← map_add,
      neg_neg, neg_add_eq_sub]
    exact hc2
  set I := ∫ y, Tr C φ0 y * (starRingEnd ℂ) (Tr C' φ0 y) ∂μ
  have h0 : (1 - ψ0 (entryForm c i0 j (-C)) * (starRingEnd ℂ) (ψ0 (entryForm c i0 j (-C')))) * I = 0 := by
    linear_combination hI
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hA))

end GlobalTheory.HeisUnit

namespace GlobalTheory.HeisUnit

theorem tr_cosetRep_orth {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ) (hψc : Continuous ψ0) (hψ1 : ψ0 ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd k n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res k 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 :=
  orth_of_charsep ψ0 (GlobalTheory.CharSep.unitary_and_separates ψ0 hψc hψ1) ι hι Tr hTr Mu hMu hMuI φ0 hφ0 hι0 ϖ hϖ i0 T T'
    hTT μ hμ

end GlobalTheory.HeisUnit
end
end

open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    ∀ (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res k 1), T ≠ T' →
    ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by
  atlas_forward_decl GlobalTheory.HeisUnit.tr_cosetRep_orth
end

section
open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

theorem intInd_apply {n d : ℕ} (M : Matrix (Fin n) (Fin d) k) :
    intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
  classical
  simp only [intInd, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]

theorem sub_inv_mul_out_mem_iff {ϖ : kˣ} (hϖ : SplitFlip.IsUnif ϖ) (y : k) (t : SplitFlip.Res k 1) :
    y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
      ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by
  have ht : t = Ideal.Quotient.mk _ (Quotient.out t) := (Quotient.out_eq t).symm
  set a := Quotient.out t
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  constructor
  · intro hc
    have hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a := by field_simp; ring
    have hmem : (ϖ : k) * y ∈ 𝒪[k] := hy ▸ add_mem (mul_mem hϖ.mem hc) a.2
    refine ⟨hmem, ?_⟩
    rw [ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
    refine ⟨-⟨_, hc⟩, Subtype.ext ?_⟩
    push_cast
    field_simp
    ring
  · rintro ⟨h, e⟩
    have e' := ht.symm.trans e
    rw [Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at e'
    obtain ⟨c, hc⟩ := e'
    have hc' : (c : k) * ϖ = a - ϖ * y := by simpa using congrArg Subtype.val hc
    have hinv : (ϖ : k)⁻¹ * ϖ = 1 := inv_mul_cancel₀ hϖ0
    have : y - (ϖ : k)⁻¹ * a = -(c : k) := by
      linear_combination (ϖ : k)⁻¹ * hc' - (y + c) * hinv
    rw [this]
    exact neg_mem c.2

theorem intInd_diagAt_eq_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (Y : Matrix (Fin n) (Fin d) k),
    GlobalTheory.HeisUnit.intInd k n d ((GlobalTheory.HeisUnit.diagAt ϖ i0).valᵀ * Y) =
      ∑ T : Fin d → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.HeisUnit.intInd k n d (Y + GlobalTheory.HeisUnit.cosetRep ϖ i0 T) := by
  intro k _ _ _ _ n d ϖ hϖ i0 Y
  classical
  have hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j := by
    intro i j
    rw [diagAt_val, diagonal_transpose, diagonal_mul]
  have hR : ∀ (T : Fin d → SplitFlip.Res k 1) i j, (Y + cosetRep ϖ i0 T) i j =
      if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j := by
    intro T i j
    simp only [cosetRep, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> ring
  by_cases hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]
  · obtain ⟨hQ, hRR⟩ := hQR
    let T0 : Fin d → SplitFlip.Res k 1 := fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩
    have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1 := by
      rw [intInd_apply, if_pos]
      intro i j
      rw [hL]
      split_ifs with h
      · subst h; exact hRR j
      · rw [one_mul]; exact hQ i j h
    have hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0 := by
      intro T
      rw [intInd_apply]
      by_cases hT : T = T0
      · rw [if_pos hT, if_pos]
        intro i j
        rw [hR]
        split_ifs with h
        · subst h; exact (sub_inv_mul_out_mem_iff hϖ _ _).2 ⟨hRR j, by rw [hT]⟩
        · exact hQ i j h
      · rw [if_neg hT, if_neg]
        intro hm
        apply hT
        funext j
        have := hm i0 j
        rw [hR, if_pos rfl] at this
        obtain ⟨_, e⟩ := (sub_inv_mul_out_mem_iff hϖ _ _).1 this
        exact e
    rw [hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']
    simp
  · have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0 := by
      rw [intInd_apply, if_neg]
      intro hm
      refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
      · have := hm i j; rwa [hL, if_neg h, one_mul] at this
      · have := hm i0 j; rwa [hL, if_pos rfl] at this
    rw [hl]
    symm
    apply Finset.sum_eq_zero
    intro T _
    rw [intInd_apply, if_neg]
    intro hm
    refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
    · have := hm i j; rwa [hR, if_neg h] at this
    · have := hm i0 j
      rw [hR, if_pos rfl] at this
      exact ((sub_inv_mul_out_mem_iff hϖ _ _).1 this).1

end GlobalTheory.HeisUnit
end

section
section
open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.HeisUnit

theorem normSq_unif_mul_resCard_pow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d → φ0 ≠ 0 →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n),
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ T T' : Fin d → GlobalTheory.SplitFlip.Res k 1, T ≠ T' →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0) →
    ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 := by
  intro k _ _ _ _ n d ι hinj Tr hTr hTrIso S hS hSiso χ hχ φ0 hφ0 hι0 hne ϖ hϖ i0 horth
  classical
  set F := ∑ T : Fin d → SplitFlip.Res k 1, Tr (cosetRep ϖ i0 T) φ0 with hF
  have hFSB : F ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.sum_mem _ fun T _ => (hTr _ φ0 hφ0).1
  have hSg : S (diagAt ϖ i0) φ0 = (χ ϖ : ℂ) • F := by
    apply hinj (hS _ φ0 hφ0) (Submodule.smul_mem _ _ hFSB)
    rw [hχ _ φ0 hφ0, map_smul, map_sum, det_diagAt, hι0]
    funext Y
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hTr _ φ0 hφ0).2, hι0]
    rw [intInd_diagAt_eq_sum ϖ hϖ]

  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → k) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hiso := hSiso (diagAt ϖ i0) φ0 hφ0 μ hμ
  rw [hSg] at hiso
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at hiso
  rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm])] at hiso
  obtain ⟨hFtop, hFint, -, hFi⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ F hFSB
  obtain ⟨h0top, h0int, h0ne, -⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0
  have hN0 : (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0ne hne, h0top⟩
  have hint : ∀ T T' : Fin d → SplitFlip.Res k 1, Integrable (fun y => Tr (cosetRep ϖ i0 T) φ0 y *
      (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y)) μ := fun T T' =>
    (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ _ (hTr _ φ0 hφ0).1).2.2.2 _ (hTr _ φ0 hφ0).1
  have hsum : ∫ y, F y * (starRingEnd ℂ) (F y) ∂μ =
      (Fintype.card (Fin d → SplitFlip.Res k 1) : ℂ) * ∫ y, φ0 y * (starRingEnd ℂ) (φ0 y) ∂μ := by
    have hpt : ∀ y, F y * (starRingEnd ℂ) (F y) = ∑ T : Fin d → SplitFlip.Res k 1, ∑ T' : Fin d → SplitFlip.Res k 1,
        Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) := by
      intro y
      rw [hF, Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun T _ => integrable_finsetSum _ fun T' _ => hint T T']
    simp_rw [integral_finsetSum _ fun T' _ => hint _ T']
    rw [Finset.card_univ.symm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_eq_single T (fun T' _ hT' => horth μ hμ T T' (Ne.symm hT')) (fun h => absurd (Finset.mem_univ _) h)]
    exact hTrIso μ hμ _ φ0 hφ0 φ0 hφ0
  rw [hFint, h0int] at hsum
  have hLF : (∫⁻ y, ‖F y‖ₑ ^ 2 ∂μ).toReal =
      (Fintype.card (Fin d → SplitFlip.Res k 1) : ℝ) * (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal := by
    exact_mod_cast hsum
  have hiso' := congrArg ENNReal.toReal hiso
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, hLF] at hiso'
  have hcard : (Fintype.card (Fin d → SplitFlip.Res k 1) : ℝ) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card]
    have : Nat.card (SplitFlip.Res k 1) = GlobalTheory.SplitWeil.resCard k :=
      Nat.card_congr (Ideal.quotEquivOfEq (pow_one 𝓂[k])).toEquiv
    rw [this]; push_cast; ring
  rw [hcard] at hiso'
  apply mul_right_cancel₀ hN0
  linear_combination hiso'

end GlobalTheory.HeisUnit
end

open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d → φ0 ≠ 0 →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n),
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ T T' : Fin d → GlobalTheory.SplitFlip.Res k 1, T ≠ T' →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0) →
    ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 := by
  atlas_forward_decl GlobalTheory.HeisUnit.normSq_unif_mul_resCard_pow_eq_one
end

section
section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharNormHalf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def normTwist (d : ℕ) (χ : kˣ →* ℂˣ) : kˣ →* ℂˣ where
  toFun x := Units.mk0 (((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)))
    (mul_ne_zero (by exact_mod_cast (norm_ne_zero_iff.2 (χ x).ne_zero)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, Units.val_mk0, GlobalTheory.SplitFlip.apow_mul]
    ring

theorem normTwist_apply (d : ℕ) (χ : kˣ →* ℂˣ) (x : kˣ) :
    (normTwist d χ x : ℂ) = ((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := rfl

theorem norm_mul_apow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  intro k _ _ _ _ d χ hu ϖ hϖ hn x
  set B := normTwist d χ
  have hunr : ∀ y : kˣ, valuation k (y : k) = 1 → B y = 1 := by
    intro y hy
    ext
    rw [normTwist_apply, hu y hy, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hy]
    simp
  have hq : (1 : ℝ) < (GlobalTheory.SplitWeil.resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard (k := k)
  set q : ℝ := (GlobalTheory.SplitWeil.resCard k : ℝ) with hqdef
  have hq0 : 0 < q := by linarith
  have hnabs : GlobalTheory.SplitWeil.nabs k ϖ = q⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.SmGL.ord_eq_one hϖ]
    simp [hqdef]
  have hap : GlobalTheory.SplitFlip.apow ϖ (-((d : ℂ) / 2)) = ((q ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [GlobalTheory.SplitFlip.apow, hnabs, show (-((d : ℂ) / 2)) = ((-((d : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (inv_nonneg.2 hq0.le), Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le, neg_neg]
  have hBϖ : B ϖ = 1 := by
    ext
    rw [normTwist_apply, hap, Units.val_one, ← Complex.ofReal_mul]
    have hb0 : 0 ≤ ‖(χ ϖ : ℂ)‖ * q ^ ((d : ℝ) / 2) := by positivity
    have hsq : (‖(χ ϖ : ℂ)‖ * q ^ ((d : ℝ) / 2)) ^ 2 = 1 := by
      rw [mul_pow, ← Real.rpow_natCast (q ^ ((d : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le]
      rw [show (d : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      exact hn
    have := (pow_eq_one_iff_of_nonneg hb0 two_ne_zero).1 hsq
    rw [this]; simp
  have hB := GlobalTheory.SmGL.eq_unrChar (χ := B) hunr hϖ
  have hx : B x = 1 := by
    rw [hB, hBϖ, GlobalTheory.SmGL.unrChar_apply, _root_.one_zpow]
  have hx' : ‖(B x : ℂ)‖ = 1 := by rw [hx]; simp
  rw [normTwist_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hx'
  rw [norm_mul]; exact hx'

end GlobalTheory.CharNormHalf
end
end

open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  atlas_forward_decl GlobalTheory.CharNormHalf.norm_mul_apow_eq_one
end

section
section
open MeasureTheory Matrix

namespace GlobalTheory.HeisUnit

theorem exists_unitary_factor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
      (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  intro k _ _ _ _ n d ψ0 hψc hψ1 ι hι Tr Mu hTr hMu hTrI hMuI S hS hSI χ hχ
  let ν : kˣ →* ℂˣ := χ *
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  have hν : ∀ x : kˣ, (ν x : ℂ) = (χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := fun x => rfl
  have hfac : ∀ x : kˣ, (χ x : ℂ) = ν x * GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2) := fun x => by
    rw [hν, mul_assoc, ← GlobalTheory.SplitFlip.apow_add, neg_add_cancel, GlobalTheory.SplitFlip.apow_zero, mul_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, fun x => by simp, fun g => ?_⟩
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  · refine ⟨ν, fun x => ?_, fun g => hfac _⟩
    let i0 : Fin n := ⟨0, hn⟩
    obtain ⟨φ0, hφ0, hιφ0⟩ := hι.surjOn (GlobalTheory.HeisUnit.intInd_mem_SB (k := k) n d)
    have hne : φ0 ≠ 0 := by
      rintro rfl
      have h := congrFun hιφ0 0
      rw [map_zero, GlobalTheory.HeisUnit.intInd_zero] at h
      exact zero_ne_one h
    have hN : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤ := fun μ hμ =>
      ⟨(GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).2.2.1 hne, (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).1⟩
    have hU := GlobalTheory.T.norm_character_unit_eq_one_heisenberg ι hι.injOn S hS hSI χ hχ φ0 hφ0 hιφ0 hN i0
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
    have hP := GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one ι hι.injOn Tr hTr hTrI S hS hSI χ hχ φ0 hφ0 hιφ0 hne ϖ hϖ i0
      (fun μ hμ T T' h => GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal ψ0 hψc hψ1 ι hι.injOn Tr hTr Mu hMu hMuI φ0 hφ0 hιφ0 ϖ hϖ i0 T T' h μ hμ)
    rw [hν]
    exact GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one d χ hU ϖ hϖ hP x

end GlobalTheory.HeisUnit
end

open MeasureTheory Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_weilCharacter_det_eq_abs_det_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
      (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  atlas_forward_decl GlobalTheory.HeisUnit.exists_unitary_factor
end

section
open MeasureTheory Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  first | exact @GlobalTheory.schr_unitary | exact GlobalTheory.schr_unitary | (intros; apply GlobalTheory.schr_unitary <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem GlobalTheory.LinModelLocal.exists_omB_of_linBar : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ') →
    (∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ)) →
    (∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = omB ν α g 1 (ι φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char Bs Γ X om om' hTr K hK S h1 h4
  by_cases hex : ∃ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι
  swap
  · exact ⟨1, 1, fun x => by simp, fun ι hι => absurd ⟨ι, hι⟩ hex⟩
  obtain ⟨ι₀, hι₀⟩ := hex
  obtain ⟨hT0, hM0, hST0, hSM0⟩ := hA ι₀ hι₀
  have hbij0 := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι₀
  have hU0 : ∀ (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) w φ ∈ GlobalTheory.WeilM.SB _ :=
    fun w => GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc w
  have key1 : ∀ (h : GL (Fin a') (Fv F Bs.v₁)) (Y : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)),
      h.valᵀ * (((h⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y) = Y := by
    intro h Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
  have key2 : ∀ (h : GL (Fin a') (Fv F Bs.v₁)) (Y : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)),
      ((h⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * (h.valᵀ * Y) = Y := by
    intro h Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  have hc : ∀ g : GL (Fin a') (Fv F Bs.v₁), ∃ c : ℂ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
      (fun Y => ι₀ (S g φ) (((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y)) = c • ι₀ φ := by
    intro g
    refine GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀
      (fun φ Y => ι₀ (S g φ) (((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y)) hbij0 ?_
      (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
      (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l)) ?_ ?_
    · intro x hx y hy c
      funext Y
      simp only [hlin g x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    · intro C x hx
      refine ⟨hU0 _ x hx, hT0 C x hx, ?_⟩
      funext Y
      simp only [hST0 g C x hx, Matrix.mul_add]
    · intro l x hx
      refine ⟨hU0 _ x hx, hM0 l x hx, ?_⟩
      funext Y
      simp only [hSM0 g l x hx, key1]
  choose c hc using hc
  have hrel : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
      ι₀ (S g φ) = fun Y => c g * ι₀ φ (g.valᵀ * Y) := by
    intro g φ hφ
    funext Y
    have := congrFun (hc g φ hφ) (g.valᵀ * Y)
    simp only [key2, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hvac := (hTr.geo.hM'.vac Bs.v₁)
  set φv := Γ.M'.vac Bs.v₁
  have hφv : φv ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁) := hvac.1
  have hιv : ι₀ φv ≠ 0 := by
    intro h0
    exact hvac.2.1 (hbij0.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  have hmul : ∀ g g', c (g * g') = c g * c g' := by
    intro g g'
    have e := congrFun (congrArg ι₀ (h2 g g' φv hφv)) ((((g * g')⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y₀)
    rw [hrel (g * g') φv hφv, hrel g (S g' φv) (h1 g' φv hφv), hrel g' φv hφv] at e
    beta_reduce at e
    have e2 : (g'.val)ᵀ * ((g.val)ᵀ * ((((g * g')⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y₀)) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, key1]
    rw [key1 (g * g') Y₀, e2] at e
    exact mul_right_cancel₀ hY₀ (e.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have e := congrFun (congrArg ι₀ (h3 φv hφv)) Y₀
    rw [hrel _ _ hφv] at e
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e
  let cH : GL (Fin a') (Fv F Bs.v₁) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  have h2ne : (2 : Fv F Bs.v₁) ≠ 0 := (isUnit_of_invertible (2 : Fv F Bs.v₁)).ne_zero
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero h2ne cH.toHomUnits
  have hcχ : ∀ g, c g = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) := fun g => by
    rw [← hχ g]; rfl
  obtain ⟨ν, hν1, hν⟩ := GlobalTheory.T.abs_weilCharacter_det_eq_abs_det_pow (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀ hbij0
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l))
    (fun C φ hφ => ⟨hU0 _ φ hφ, hT0 C φ hφ⟩) (fun l φ hφ => ⟨hU0 _ φ hφ, hM0 l φ hφ⟩)
    (fun μ hμ C φ _ φ' _ => GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving _ hψc μ hμ _ φ φ') (fun μ hμ l φ _ φ' _ => GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving _ hψc μ hμ _ φ φ')
    S h1 h5 χ (fun g φ hφ => by rw [hrel g φ hφ, hcχ g])
  refine ⟨ν, 1, hν1, ?_⟩
  intro ι hι g φ hφ
  obtain ⟨hT, hM, -, -⟩ := hA ι hι
  obtain ⟨c', hc'⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀
    ι hbij0 (fun x _ y _ c => by rw [map_add, map_smul])
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l))
    (fun C x hx => ⟨hU0 _ x hx, hT0 C x hx, hT C x hx⟩) (fun l x hx => ⟨hU0 _ x hx, hM0 l x hx, hM l x hx⟩)
  rw [hc' _ (h1 g φ hφ), hc' φ hφ, hrel g φ hφ, hcχ g, hν g]
  funext Y
  simp only [omB, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, Matrix.mul_one, Fintype.card_fin, gdet,
    MonoidHom.one_apply, apow_one]
  push_cast
  ring
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ') →
    (∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ)) →
    (∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = omB ν α g 1 (ι φ) := by
  atlas_forward_decl GlobalTheory.LinModelLocal.exists_omB_of_linBar
end
