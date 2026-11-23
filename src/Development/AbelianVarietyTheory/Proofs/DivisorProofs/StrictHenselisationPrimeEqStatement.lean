module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationPrimeEq
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.strict_henselisation_prime_eq : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j ∧
      ∃ (D₁ : Type) (_ : CommRing D₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁)
        (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ ∧
        ∀ σ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ →
          Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_torsor) | (exact GlobalTheory.KeyOriginCut.exists_stage_torsor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_torsor  <;> assumption)
