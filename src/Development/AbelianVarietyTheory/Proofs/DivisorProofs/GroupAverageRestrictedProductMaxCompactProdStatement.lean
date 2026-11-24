module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ), (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) → avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) = ∏ᶠ v, avg (u v) := by
  first | exact @GlobalTheory.AvgRestr.avg_restr_prod | exact GlobalTheory.AvgRestr.avg_restr_prod | (intros; apply GlobalTheory.AvgRestr.avg_restr_prod <;> assumption)
