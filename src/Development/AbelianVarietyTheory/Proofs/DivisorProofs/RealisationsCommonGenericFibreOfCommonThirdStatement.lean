module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsCommonGenericFibreOfCommonThird
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.realisations_common_generic_fibre_of_common_third : ∀ (o Ω o₁ o₂ Ω' : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o₁] [CommRing o₂] [Field Ω'] [Algebra o₁ Ω'] [Algebra o₂ Ω'] (S : ThetaSys o Ω) (S₁ : ThetaSys o₁ Ω') (S₂ : ThetaSys o₂ Ω') (ρ : S.Real) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (lab₁ : S.Gam → S₁.Gam) (lab₂ : S.Gam → S₂.Gam) (φ : Ω →+* Ω'), Same ρ ε ρ₁ ε₁ lab₁ φ → Same ρ ε ρ₂ ε₂ lab₂ φ → SameAt ρ₁.P ρ₂.P S₁.R.val.toRingHom S₂.R.val.toRingHom ε₁ ε₂ (fun x => ρ₁.pt (lab₁ x)) (fun x => ρ₂.pt (lab₂ x)) := by
  first | exact @GlobalTheory.Poinc.SameComb.combine | exact GlobalTheory.Poinc.SameComb.combine | (intros; apply GlobalTheory.Poinc.SameComb.combine <;> assumption)
