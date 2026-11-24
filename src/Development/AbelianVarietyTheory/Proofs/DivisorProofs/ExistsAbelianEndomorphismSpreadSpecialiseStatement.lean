module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianEndomorphismSpreadSpecialise
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_abelian_endomorphism_spread_specialise : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B, IsMonHom f → ∃ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ ∧ IsMonHom f₀ ∧ GlobalTheory.Spread.bcMap B.hom R.val ≫ Ψ.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ ∧ σ ≫ pullback.fst _ _ = 𝟙 _ ∧ σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom ∧ f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.Spread.exists_endo_spread_specialise | exact GlobalTheory.Spread.exists_endo_spread_specialise | (intros; apply GlobalTheory.Spread.exists_endo_spread_specialise <;> assumption)
