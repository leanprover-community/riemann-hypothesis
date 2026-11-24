module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellPosExact
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

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def cellLocSys {S : Type} [CommRing S] {X : Type} {Ω : Type} [Field Ω] [Algebra S Ω] (G : X → Submodule S Ω)
    (f : Ω) : X → Submodule S Ω :=
  fun I => ⨆ n : ℕ, (G I).comap (LinearMap.mulLeft S (f ^ n))

def CellLocGlue.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (R : Subring Ω) (m : ℕ) (f u : Fin m → Ω),
    (∀ l, f l ∈ R) → (∀ l, u l ∈ R) → ∑ l, u l * f l = 1 →
    (∀ I, ∀ r ∈ R, ∀ a ∈ G I, r * a ∈ G I) →
    (∀ l, CellPosExact S y (cellLocSys G (f l))) →
    CellPosExact S y G

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
