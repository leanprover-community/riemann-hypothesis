module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibility
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.isClosedImmersion_of_coordinate_divisibility : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  first | exact @GlobalTheory.ZH.RatModel.immBy_of_div | exact GlobalTheory.ZH.RatModel.immBy_of_div | (intros; apply GlobalTheory.ZH.RatModel.immBy_of_div <;> assumption)
