module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSubringModelAbelianLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetGeneratorDescendsSubringStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmLineBundleIsoDescendsSubringFinsetStatement
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegApprox

open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem model_exists : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (F : Finset R), IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P₀ : LB (G2 B).left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) := GlobalTheory.T.exists_finiteType_subring_model_abelian_lineBundle

theorem rig_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := GlobalTheory.T.exists_finset_generator_descends_subring

theorem symm_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := GlobalTheory.T.symm_lineBundleIso_descends_subring_finset

end GlobalTheory.SiegApprox
