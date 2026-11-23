module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_neronNeutralComponent_finite_level : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [Algebra K K'], SH R K' → (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ P : Out.PolAV (Sp K), ∃ (s : Finset R) (c : ℕ), 1 ≤ c ∧ ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (L : Type) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (_ : Algebra K L), SmConn G ∧ (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsModel (L := L) P.A G ∧ SmoothOfRelativeDimension P.g G.hom ∧ (∃ N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N) ∧ ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left := by
  first | exact @GlobalTheory.NeutralLevel.exists_level_model | exact GlobalTheory.NeutralLevel.exists_level_model | (intros; apply GlobalTheory.NeutralLevel.exists_level_model <;> assumption)
