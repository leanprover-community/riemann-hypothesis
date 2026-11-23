module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralOfEtaleFaithfullyFlatCover
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.geom_integral_of_etale_faithfully_flat_cover : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R R₁ : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁] (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (σ₁ : K₁ →ₐ[K] ℂ) (p : R₁ →ₐ[K] ℂ) (q : R →ₐ[K] K₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) → (∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _) e) → ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (j : R₁ →+* S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (ii : K₁ →+* k), GeomInt k S ∧ s.comp j = p.toRingHom ∧ (s₀.toRingHom.comp j).comp (algebraMap R R₁) = ii.comp q.toRingHom := by
  first | exact @GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale | exact GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale | (intros; apply GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale <;> assumption)
