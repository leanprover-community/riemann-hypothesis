module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelMapKernelEqIntegralTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormLtOneOfIrreducible
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem labels_exist : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → Nonempty u.Lab := by
  intro h₁ h₂ h₃ o Ω _ _ _ _ S ρ p _ y₀ u hy
  obtain ⟨q, hq, hq'⟩ := GlobalTheory.ZH.PsiForm.main o Ω S ρ p y₀ u
  obtain ⟨yy, hs, he⟩ := GlobalTheory.T.exists_labelMap_torsion_characters h₁ h₂ h₃ o Ω S ρ p y₀ u
  have hk := GlobalTheory.T.label_map_kernel_eq_integral_torsion h₁ h₂ h₃ o Ω S ρ p y₀ u yy hs he hy
  obtain ⟨hi, wt, hw⟩ := GlobalTheory.T.isoFree_perp_labelKernel_weights h₁ h₂ h₃ o Ω S ρ p y₀ u yy hs he
  exact ⟨⟨q, hq, hq', yy, hs, he, hk, hi, wt, hw⟩⟩

end GlobalTheory.ZH
