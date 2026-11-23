module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxSubRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {Λ R : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] (a : O →+* Λ) (A : Subalgebra Λ R) (D : RD Φ R), (∀ g i j, D.r g i j ∈ A) → (∀ v i s, D.ψ v i s ∈ A) → Φ.IsRep ((algebraMap Λ R).comp a) D.r → ∃ D' : RD Φ A, D'.map (A.val : A →+* R) = D ∧ Φ.IsRep ((algebraMap Λ A).comp a) D'.r := by
  intro O Γ _ _ Φ Λ R _ _ _ a A D hr hψ h
  have h1 : ∀ i j : Fin 4, (((1 : M4 A) i j : A) : R) = (1 : M4 R) i j := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  let r' : Γ →* M4 A :=
    { toFun := fun g => Matrix.of fun i j => ⟨D.r g i j, hr g i j⟩
      map_one' := by
        ext i j
        rw [h1]; simp
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  have hr' : ∀ g i j, ((r' g i j : A) : R) = D.r g i j := fun _ _ _ => rfl
  refine ⟨⟨r', fun v i => (D.ψ v i).codRestrict A (hψ v i)⟩, ?_, fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩
  · refine RD.ext ?_ ?_
    · ext g i j; rfl
    · funext v i; ext s; rfl
  · have := h.mult g
    unfold IsGSp at this ⊢
    ext i j
    have e := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul, MulMemClass.coe_mul, h1]
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    refine Eq.trans ?_ e
    simp [Matrix.mul_apply, adj, hr']
  · ext i j
    rw [h1]
    show D.r g i j = _
    rw [h.kill g hg]
  · exact Subtype.ext (h.nrm hij)
