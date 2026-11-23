module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
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
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.semiAbelian_reduction_along_isogeny_strict_henselian : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] (G' : Over (Sp R)) [GrpObj G'] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → IsSemiAbelian G' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G').hom → ∀ (i : A ⟶ (Over.pullback (spMap (algebraMap R K))).obj G') (r : (Over.pullback (spMap (algebraMap R K))).obj G' ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → ∃ (G : Over (Sp R)) (_ : GrpObj G) (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ A), SmConn G ∧ IsMonHom e.hom ∧ Nonempty (TorusExtension (spFibre G)) := by
  first | exact @GlobalTheory.IsogRed.semiAbelian_reduction_of_isogeny | exact GlobalTheory.IsogRed.semiAbelian_reduction_of_isogeny | (intros; apply GlobalTheory.IsogRed.semiAbelian_reduction_of_isogeny <;> assumption)
