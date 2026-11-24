module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpen
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

theorem _root_.GlobalTheory.T.exists_basicOpen_factor_fieldPoint_affineOpen : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  first | exact @GlobalTheory.SS.ArcInf.exists_basicOpen_factor | exact GlobalTheory.SS.ArcInf.exists_basicOpen_factor | (intros; apply GlobalTheory.SS.ArcInf.exists_basicOpen_factor <;> assumption)
