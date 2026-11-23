module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

def Bdd {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (G : La) (F : ι → Y → ℂ) : Prop :=
  ∃ C : ℝ, ∀ y, A.nsq G F y ≤ C

structure Cusp {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) where
  conn : ConnectedSpace Y
  la1 : Y → ℝ
  first_minimum_pos : ∀ y, 0 < la1 y
  vol_fin : A.mu Set.univ < ⊤
  van : La → ℝ → (ι → Y → ℂ) → Prop
  van_zero : ∀ G c, van G c (fun _ _ => 0)
  van_add : ∀ G c F F', A.IsSec G F → A.IsSec G F' → van G c F → van G c F' →
    van G c (fun i y => F i y + F' i y)
  van_smul : ∀ G c (a : ℂ) F, A.IsSec G F → van G c F → van G c (fun i y => a * F i y)
  van_anti : ∀ G c c' F, c' ≤ c → van G c F → van G c' F

  van_mul : ∀ G G' c F F', A.IsSec G F → A.IsSec G' F' → Bdd A G F → Bdd A G' F' →
    van G c F → van (G + G') c (fun i y => F i y * F' i y)

  kd : ℝ
  two_lt_kd : 2 < kd
  dec : ∀ G F (c : ℝ), A.IsSec G F → Bdd A G F → van G c F →
    ∃ C : ℝ, ∀ y, A.nsq G F y ≤ C * Real.exp (-(kd * c) / la1 y ^ 2)
  gap : ∀ G F, A.IsSec G F → Bdd A G F → van G 0 F → ∃ c : ℝ, 0 < c ∧ van G c F
  cfw : (Y → ℝ) → ℝ → Prop
  cfw_zero : cfw (fun _ => 0) 0
  cfw_smul : ∀ ps a (t : ℝ), 1 ≤ t → cfw ps a → cfw (fun y => t * ps y) (t * a)

  cf : ∀ (G L : La) (N : ℕ) (w : Fin N → ι → Y → ℂ) (F : ι → Y → ℂ) (ps : Y → ℝ) (a η : ℝ),
    (∀ k, A.IsSec L (w k)) → (∀ k, Bdd A L (w k)) → (∀ k, van L 0 (w k)) →
    (∀ y, ∃ k, w k (A.pick y) y ≠ 0) → 0 < η → 0 ≤ a → A.IsSec G F → cfw ps a →
    ∫⁻ y, ENNReal.ofReal (A.nsq G F y * Real.exp (-ps y) * A.sqn L w y ^ (-η)) ∂A.mu < ⊤ →
    Bdd A G F ∧ van G 0 F ∧ van G a F

end

end ReciprocityTheory.ChartRestriction.G.AR
