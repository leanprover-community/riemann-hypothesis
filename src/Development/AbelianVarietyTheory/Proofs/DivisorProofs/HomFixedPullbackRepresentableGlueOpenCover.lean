module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedBundlePullbackIsoOfLocalIsoAbelianHom
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem homFixRep_glue_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (J : Type) (U : J → S.Opens), (∀ p : S, ∃ i, p ∈ U i) → (∀ i, ∃ (AU : Over (U i).toScheme) (_ : GrpObj AU) (BU : Over (U i).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U i).ι φA ∧ IsGrpPullback BU B (U i).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB J U hU hloc
  refine GlobalTheory.T.homFixedPullback_representable_glue (fun H A B _ _ _ _ L M Φ hΦ hA hB hL hM rA rB h => GlobalTheory.HomFixLocal.lbIso_pull_of_local H A B L M Φ hΦ hA hB hL hM rA rB h) S A B L M hA hB hL hM rA rB J (fun i => (U i).toScheme) (fun i => (U i).ι) (fun i => inferInstance) (fun s => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := hU s; exact ⟨i, by simpa [Scheme.Opens.range_ι] using hi⟩
  · obtain ⟨AU, gA, BU, gB, φA, φB, pA, pB, R, h1, h2, h3⟩ := hloc i; exact ⟨AU, BU, gA, gB, φA, φB, R, pA, pB, h1, h2, h3⟩

end GlobalTheory
