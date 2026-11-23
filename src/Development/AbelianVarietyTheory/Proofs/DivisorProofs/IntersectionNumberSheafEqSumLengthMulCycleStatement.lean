module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycle
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

theorem _root_.GlobalTheory.T.intersectionNumber_sheaf_eq_sum_length_mul_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | exact GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | (intros; apply GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed <;> assumption)
