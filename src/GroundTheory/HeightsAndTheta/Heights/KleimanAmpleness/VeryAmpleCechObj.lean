module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
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

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section Aug

variable (S : Type u) [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {n : ℕ}

def Cech.AugExact {y : Fin (n + 1) → Ω} (G : Chart y → Submodule S E) (B : Submodule S E) : Prop :=
  (∀ J, B ≤ G J) ∧
  (∀ b ∈ B, (∀ _ : Cech.Idx (support y) 0, b = 0) → b = 0) ∧
  (∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G 0,
      Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) 0 s = 0 → ∃ b ∈ B, ∀ J, s J = b) ∧
  ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G (p + 1),
    Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) (p + 1) s = 0 →
      ∃ t ∈ Cech.Cdeg (fun _ : Chart y => E) G p,
        Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) p t = s

end Aug

section Z

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E] {r : ℕ}

def secsOnZChart (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (I : Chart x)
    (J : Chart h) : Submodule S E :=
  Submodule.span S {e | ∃ n : ℕ, xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I}

def secsOnZ (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (J : Chart h) : Submodule S E :=
  ⨅ I : Chart x, secsOnZChart G H h I J

end Z

end

end GroundTheory.Heights₂.Heights.Kleiman
