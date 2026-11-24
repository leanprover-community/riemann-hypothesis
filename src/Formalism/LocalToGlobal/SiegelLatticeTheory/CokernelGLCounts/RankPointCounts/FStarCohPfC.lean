module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfB
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem split_finite : {p : PlF D | (Zd.M p).split.isSome}.Finite := by
  have hfinite (ℓ : ℕ) : {p : PlF D | Loc.resChar p = ℓ}.Finite := by
    have hsub : {p : PlF D | Loc.resChar p = ℓ} ⊆
        {v | v.asIdeal ∣ Ideal.span {(ℓ : 𝓞 D.host.F)}} := by
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      rw [Ideal.dvd_span_singleton, ← hp, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact ringChar.Nat.cast_ringChar
    by_cases hℓ : ℓ = 0
    · subst hℓ
      convert Set.finite_empty
      rename_i p
      change Loc.resChar p = 0 ↔ False
      simp only [iff_false]
      intro hp
      have h1 : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.absNorm_mem p.asIdeal
      have hc : CharP (𝓞 D.host.F ⧸ p.asIdeal) 0 := by
        have h2 := ringChar.charP (𝓞 D.host.F ⧸ p.asIdeal)
        unfold Loc.resChar at hp
        rwa [hp] at h2
      rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at h1
      exact p.ne_bot h1
    · refine (Ideal.finite_factors ?_).subset hsub
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hℓ
  refine ((hfinite (D.host.g 0)).union (hfinite (D.host.g 1))).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have hs : (D.s.atP p).split.isSome := by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hp
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hg] at hA
    cases h2 : (D.s.atP p).split with
    | none =>
      rw [h2] at hA
      exact (hA : False).elim
    | some sg => rfl
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (D.s_split p).1 hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hin
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  exact hin

theorem cohIota_holds : CohIota Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' _
  refine (split_finite Zd).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq]
  by_contra hn
  apply hp
  intro g hg
  rw [hg] at hn
  exact (hn rfl).elim

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
