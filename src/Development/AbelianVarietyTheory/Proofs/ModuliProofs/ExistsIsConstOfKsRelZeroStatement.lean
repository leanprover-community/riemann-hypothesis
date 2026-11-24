module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstOfKsRelZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_isConst_of_ksRel_zero' : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (φ : A'.left ⟶ A.left) (j : P₀.A.left ⟶ A'.left) (s : (Fin P₀.g → ℂ) → ∀ W : A.left.Opens, Γ(A.left, W) → ℂ), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) φ → IsGrpPullback P₀.A A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → KSRel u A.hom (j ≫ φ) (fun r => (xD r).snd) 0 s → ∃ ρ, IsConst A' P₀.A ρ j := by
  first | exact @GlobalTheory.KS.exists_isConst_of_ksRel_zero | exact GlobalTheory.KS.exists_isConst_of_ksRel_zero | (intros; apply GlobalTheory.KS.exists_isConst_of_ksRel_zero <;> assumption)
