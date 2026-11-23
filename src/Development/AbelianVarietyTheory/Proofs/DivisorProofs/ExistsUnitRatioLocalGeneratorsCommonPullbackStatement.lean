module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRatioLocalGeneratorsCommonPullback
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unit_ratio_local_generators_common_pullback : ∀ (X' Z Z' : Scheme.{0}) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')), w.IsGen → ∀ (V' : X'.Opens) (V : Z.Opens) (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ), GlobalTheory.Pinch.LocGen L' V' a → GlobalTheory.Pinch.LocGen N V b → ∀ O : Z'.Opens, O ≤ i' ⁻¹ᵁ V' → O ≤ p' ⁻¹ᵁ V → ∃ u : Γ(Z', O)ˣ, ∀ (z : Z') (k : L'.ι) (l : N.ι), z ∈ O → i' z ∈ L'.U k → p' z ∈ N.U l → gm p' z (V ⊓ N.U l) (b l) = gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) * (gm (𝟙 Z') z O u * gm i' z (V' ⊓ L'.U k) (a k)) := by
  first | exact @GlobalTheory.Pinch.exists_ratio_unit | exact GlobalTheory.Pinch.exists_ratio_unit | (intros; apply GlobalTheory.Pinch.exists_ratio_unit <;> assumption)
