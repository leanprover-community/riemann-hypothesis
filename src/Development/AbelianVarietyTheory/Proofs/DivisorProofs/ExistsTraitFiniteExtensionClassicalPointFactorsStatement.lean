module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteExtensionClassicalPointFactors
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_trait_finiteExtension_classicalPoint_factors : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp S.R ⟶ F.X) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → ∃ (T' : Trait F) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : S.R →+* FractionRing T'.V) (e : T'.D.toPre.X ≃+ T.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₀ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.β a b = k * T.β (e a) (e b) := by
  first | exact @GlobalTheory.TraitExtLab.main | exact GlobalTheory.TraitExtLab.main | (intros; apply GlobalTheory.TraitExtLab.main <;> assumption)
