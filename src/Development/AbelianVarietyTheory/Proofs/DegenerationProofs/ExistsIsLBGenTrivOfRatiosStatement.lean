module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatios
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

theorem _root_.GlobalTheory.T.exists_isLB_genTriv_of_ratios' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | exact GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | (intros; apply GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios <;> assumption)
