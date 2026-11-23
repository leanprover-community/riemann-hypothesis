module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusExtensionDescentGaloisInvariant
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_splitTorusExtension_descent_galois_invariant : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  first | exact @GlobalTheory.exists_splitExt_of_galois_invariant | exact GlobalTheory.exists_splitExt_of_galois_invariant | (intros; apply GlobalTheory.exists_splitExt_of_galois_invariant <;> assumption)
