module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorSchemeLineBundleAffineFiniteType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.generatorScheme_lineBundle_affine_finiteType : ∀ (B : Scheme.{0}) (N : LB B), N.IsLB → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ i : N.ι, Γ(G, q ⁻¹ᵁ N.U i)ˣ), IsAffineHom q ∧ LocallyOfFiniteType q ∧ (∀ i i', res (Scheme.Hom.preimage_mono q (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (u i) = pullU q _ (N.g i i') * res (Scheme.Hom.preimage_mono q (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (u i')) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ), (∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) = pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i')) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ i, (g.appLE (q ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl)).hom (u i).val = (s i).val := by
  first | exact @GlobalTheory.generatorScheme_affine_finiteType | exact GlobalTheory.generatorScheme_affine_finiteType | (intros; apply GlobalTheory.generatorScheme_affine_finiteType <;> assumption)
