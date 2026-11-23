module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

def formOf {G : HTGroup p} (P : Pair G) : Form G := ⟨P.β, P.sym, P.trivAf, P.trivR⟩

def ofGrp {G : HTGroup p} (F : Form G) (r : grp G F.β)
    (h : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

def phi {G : HTGroup p} (q : FCls G) (Q : Cls G) : ConjClasses (grp G (Quot.out q).β) :=
  if h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β
  then ConjClasses.mk ⟨_, h.choose_spec.2⟩ else ConjClasses.mk 1

theorem phi_spec {G : HTGroup p} (q : FCls G) (Q : Cls G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y))
    (hm : ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β) :
    ∃ y₁ : G.Cˣ, ∃ s₁ : ℚ, 0 < s₁ ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s₁ * (y₁ * (Quot.out q).β * sh G y₁) ∧
      ∃ hm₁ : ((y₁⁻¹ * (Quot.out Q).γ * y₁, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β,
        phi q Q = ConjClasses.mk ⟨_, hm₁⟩ := by
  have h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β := ⟨y, ⟨s, hs, hβ⟩, hm⟩
  obtain ⟨⟨s₁, hs₁, hβ₁⟩, hm₁⟩ := h.choose_spec
  exact ⟨h.choose, s₁, hs₁, hβ₁, hm₁, by rw [phi, dite_eq_left h]⟩

end GlobalTheory.LKCx.Regroup
