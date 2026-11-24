module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

def CoreHyp {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r : ℕ} {T : E}
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V) : Prop :=
  Submodule.IsLattice E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ ∧ F0.z ∈ Λ ∧
    (∀ c : E, c • F0.z ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T) → ∃ o : 𝓞 E, (o : E) = c) ∧
    XLam Λ (⟨F0, F0.z⟩ : LFlag S r T) = Formalism.L2.SG.Saturated.latSpan aa F0.e ∧
    (∀ a, aa a ≠ 0) ∧ (∀ a, ∀ x ∈ aa a, star x ∈ aa a) ∧
    (∃ x : 𝓞 E, (x : E) + star (x : E) = 1)

def CoreStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → Formalism.L2.SG.Saturated.IsSplitBy aa F0 Λ

def AaStep : Prop :=
  ∀ D : D7, ∀ a : Fin D.R.rS, Formalism.L2.SG.Saturated.aaS D a ≠ 0 ∧
    ∀ x ∈ Formalism.L2.SG.Saturated.aaS D a, (letI := D.host.cmStar; star x) ∈ Formalism.L2.SG.Saturated.aaS D a

def TrStep : Prop :=
  ∀ D : D7, ∃ x : 𝓞 D.host.E, (x : D.host.E) + (letI := D.host.cmStar; star (x : D.host.E)) = 1

end PI.SRW
