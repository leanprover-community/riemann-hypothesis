module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientPolynomialGLFunctionNeZeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem scale_pow_eq_of_isScale {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := GlobalTheory.T.exists_coefficientPolynomial_GLFunction_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

theorem coefFn_map_eq {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)
    (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) : coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  simp only [coefFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, RingHom.id_comp]

theorem exists_fixed_of_mem_span {D : D7} (j : Fin D.R.m) {W M : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    (Φ : W →ₗ[ℂ] M) (c : VsV D j ℂ →ₗ[ℂ] W) (a₀ : ℂ) (S : Set (VV (↥D.LL0) (lamV D j))) {P : M}
    (hP : P ∈ Submodule.span (smallInt D)
      {P | ∃ Fv ∈ S, P = Φ (c (a₀ • GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv))}) :
    ∃ y : VsV D j ℂ, P = a₀ • Φ (c y) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ z, τ (Formalism.L2.Host.embLL0 D z) = Formalism.L2.Host.embLL0 D z) → ConjVec j τ y y := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Fv, -, rfl⟩ := hP
    refine ⟨GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv, by rw [c.map_smul, Φ.map_smul], fun τ hτ => ?_⟩
    change MvPolynomial.map _ _ = MvPolynomial.map _ (MvPolynomial.map _ _)
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp (Formalism.L2.Host.embLL0 D) = Formalism.L2.Host.embLL0 D from RingHom.ext hτ]
  | zero => exact ⟨0, by rw [c.map_zero, Φ.map_zero, smul_zero], fun τ _ => (map_zero _).symm⟩
  | add P₁ P₂ _ _ h1 h2 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    obtain ⟨y2, rfl, c2⟩ := h2
    refine ⟨y1 + y2, by rw [map_add c, map_add Φ, smul_add], fun τ hτ => ?_⟩
    have e1 := c1 τ hτ
    have e2 := c2 τ hτ
    unfold ConjVec at e1 e2 ⊢
    rw [Submodule.coe_add, map_add (f := _), ← e1, ← e2]
  | smul a P₁ _ h1 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    refine ⟨(a : ℂ) • y1, ?_, fun τ hτ => ?_⟩
    · rw [c.map_smul, Φ.map_smul, smul_comm a₀]
      rfl
    · have e1 := c1 τ hτ
      unfold ConjVec at e1 ⊢
      obtain ⟨o, ho⟩ := a.2
      have ha : (τ : ℂ →+* ℂ) (a : ℂ) = a := by rw [← ho]; exact hτ _
      rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← e1, ha]


end GlobalTheory.BigOn.Exp.TwConj
