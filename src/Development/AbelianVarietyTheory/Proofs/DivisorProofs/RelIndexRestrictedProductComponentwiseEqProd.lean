module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RelIdxRestr

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_iInf_comap {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (C H : ∀ v, Subgroup (Y v))
    (_hfin : ∀ v, (H v).relIndex (C v) ≠ 0) (hev : ∀ᶠ v in cofinite, C v ≤ H v) :
    (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  classical
  set S : Finset V := (Filter.eventually_cofinite.1 hev).toFinset with hS
  have hSm : ∀ v, v ∉ S → C v ≤ H v := fun v hv => by
    by_contra h; exact hv (by simpa [hS] using h)
  set Cg := ⨅ v, (C v).comap (pf v)
  set Hg := ⨅ v, (H v).comap (pf v)
  have hmemC : ∀ x : X, x ∈ Cg ↔ ∀ v, pf v x ∈ C v := fun x => by simp [Cg, Subgroup.mem_iInf]
  have hmemH : ∀ x : X, x ∈ Hg ↔ ∀ v, pf v x ∈ H v := fun x => by simp [Hg, Subgroup.mem_iInf]
  let φ : Cg →* ∀ v : S, C v := MonoidHom.pi fun v =>
    ((pf v).comp Cg.subtype).codRestrict (C v) fun x => (hmemC x).1 x.2 v
  have hφ : ∀ x (v : S), ((φ x v : C v) : Y v) = pf v x := fun _ _ => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z
      (GlobalTheory.RestrMeas.eventually_of_finset S fun v hv => by simp [z, hv, one_mem])
    have hxC : x ∈ Cg := (hmemC x).2 fun v => by
      rw [hx v]
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    refine ⟨⟨x, hxC⟩, funext fun v => Subtype.ext ?_⟩
    rw [hφ]
    show pf v x = _
    rw [hx v]
    simp [z, v.2]
  have hcomap : Hg.subgroupOf Cg = (Subgroup.pi Set.univ fun v : S => (H v).subgroupOf (C v)).comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, hmemH]
    constructor
    · intro h v; exact h v
    · intro h v
      by_cases hv : v ∈ S
      · exact h ⟨v, hv⟩
      · exact hSm v hv ((hmemC x).1 x.2 v)
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ,
    finprod_eq_prod_of_mulSupport_subset (s := S)]
  · exact (Finset.prod_coe_sort S fun v => (H v).relIndex (C v))
  · intro v hv
    by_contra h
    exact hv (Subgroup.relIndex_eq_one.2 (hSm v h))

end GlobalTheory.RelIdxRestr

end
