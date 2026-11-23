module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitExtensionDivisibleValuationForm
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_traitExtension_divisible_valuationForm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (O : Type) [CommRing O] (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∀ N : ℕ, 0 < N → ∃ (T : Formalism.L2.Pj.CDVR) (ρ : R →+* T.V) (b : O →+* T.V) (ϖ : T.V) (D' : DegData T.V (maximalIdeal T.V)), Function.Injective ρ ∧ ρ.Finite ∧ Function.Injective b ∧ Irreducible ϖ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ (∀ Q : D'.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ D'.toPre ϖ Q → ∀ u v, (N : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf D'.toPre Q u v) ∧ ∀ k : ℕ, k ∣ N → ∀ q : QkPt D'.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D'.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q := by
  first | exact @GlobalTheory.TraitInputExt.exists_ext_dvd_rational | exact GlobalTheory.TraitInputExt.exists_ext_dvd_rational | (intros; apply GlobalTheory.TraitInputExt.exists_ext_dvd_rational <;> assumption)
