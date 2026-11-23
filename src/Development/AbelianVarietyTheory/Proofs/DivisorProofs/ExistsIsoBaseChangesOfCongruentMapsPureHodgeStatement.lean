module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoBaseChangesOfCongruentMapsPureHodge
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_iso_baseChanges_of_congruent_maps_pureHodge : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (S : Type) [CommRing S] (G : Over (Sp S)) [GrpObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (W : G ⟶ G) [IsMonHom W] (r s : S), IsPureBC G W r s → ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (IsLocalRing.maximalIdeal T) T → ∀ p : ℕ, p.Prime → (p : T) ∈ IsLocalRing.maximalIdeal T → ∀ a b : S →+* T, (∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T) → IsUnit (a (r - s)) → ∀ (A : Over (Sp T)) [GrpObj A] (φ : A.left ⟶ G.left), IsGrpPullback A G (spMap a) φ → ∃ φ' : A.left ⟶ G.left, IsGrpPullback A G (spMap b) φ' ∧ ∀ x : Sp (IsLocalRing.ResidueField T) ⟶ A.left, x ≫ A.hom = spMap (IsLocalRing.residue T) → x ≫ φ = x ≫ φ' := by
  first | exact @GlobalTheory.PureTower.exists_isGrpPullback_of_congr | exact GlobalTheory.PureTower.exists_isGrpPullback_of_congr | (intros; apply GlobalTheory.PureTower.exists_isGrpPullback_of_congr <;> assumption)
