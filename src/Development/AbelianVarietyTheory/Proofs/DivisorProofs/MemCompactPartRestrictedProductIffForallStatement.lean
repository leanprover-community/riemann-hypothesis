module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForall
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


theorem _root_.GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → (∀ v, ∀ a ∈ Tv v, ∀ b ∈ Tv v, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ ∀ v, pf v x ∈ cptPart (Tv v) := by
  first | exact @GlobalTheory.CptPartRestr.mem_cptPart_iff_forall | exact GlobalTheory.CptPartRestr.mem_cptPart_iff_forall | (intros; apply GlobalTheory.CptPartRestr.mem_cptPart_iff_forall <;> assumption)
