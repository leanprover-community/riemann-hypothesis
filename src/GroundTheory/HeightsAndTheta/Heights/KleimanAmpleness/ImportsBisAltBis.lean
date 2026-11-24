module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def GradedCech.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ),
    ∃ e : ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (i : ℕ) (c : ℤ),
        IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c ≃ₗ[S] Kleiman.cohom (gradedEquiv S N M G) i c,
      (∀ (M M' : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (G' : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M')
        (f : M →ₗ[Poly S N] M') (hf : IndefiniteRowSideFullHecke.Kleiman.IsGradedHom S N G G' f) (i : ℕ) (c : ℤ)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c),
        e M' G' i c (IndefiniteRowSideFullHecke.Kleiman.gradedHmap S N hf i c z) =
          Kleiman.cohomMap (⟨f, fun c m hm => hf c m hm⟩ :
            Kleiman.GradedHom (gradedEquiv S N M G) (gradedEquiv S N M' G')) i c (e M G i c z)) ∧
      ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (m : M) (hm : m ∈ G.piece c)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G 0 c),
        (z : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) = IndefiniteRowSideFullHecke.Kleiman.unitCochain S N M m →
        e M G 0 c (Submodule.Quotient.mk z) = Kleiman.toH0 (gradedEquiv S N M G) c ⟨m, hm⟩

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
