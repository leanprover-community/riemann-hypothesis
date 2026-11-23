module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorDescentDirectedUnionSubring
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_torsor_descent_directedUnion_subring : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (q : ℕ), 0 < q →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E] (Q : Ideal E) [Q.IsPrime]
      (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (i : ι) (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (𝒜 i)) EA) (_ : Algebra (𝒜 i) EA)
      (_ : IsScalarTower (𝒜 i) (Polynomial (𝒜 i)) EA) (_ : Algebra.Etale (Polynomial (𝒜 i)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (𝒜 i)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 i).subtype) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)) →+*
          GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
        β.comp (algebraMap (Localization.AtPrime (Q.comap e))
            (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)))) =
          (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))).comp
            (Localization.localRingHom (Q.comap e) Q e rfl) ∧
      ∃ (D : Type) (_ : CommRing D) (_ : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D)
        (actA : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))] D)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D q actA ∧
        ∀ (C : Type) [CommRing C] (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* C) (σ : D →+* C),
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D) = ψ.comp β →
          ∃ σ₁ : D₁ →+* C, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  first | (exact @GlobalTheory.TorsorUnionDescent.exists_stage_torsor) | (exact GlobalTheory.TorsorUnionDescent.exists_stage_torsor) | (intros; apply GlobalTheory.TorsorUnionDescent.exists_stage_torsor  <;> assumption)
