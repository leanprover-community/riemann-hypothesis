module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycle
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

theorem _root_.GlobalTheory.T.intersectionNumber_globalSection_eq_sum_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (s : M.Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfSec hM s hs).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult | exact GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult | (intros; apply GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult <;> assumption)
