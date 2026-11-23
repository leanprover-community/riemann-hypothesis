module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
public import Mathlib.Algebra.Lie.OfAssociative
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsoluteGaloisMemFixingSubgroupMaxUnramified
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

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Hyp

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime] (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem actVB_res (Y : Lat K LL) (g : ↥(GK K)) (g' : ↥(GK (levelField K s))) (hg : (g : GQ l) = g') :
    actVB ((LT l).PD K) Y.ρ g = actVB ((LT l).PD (levelField K s)) (resKs h Y) g' := by
  have h2 : Y.ρ g = resKs h Y g' := congrArg Y.ρ (Subtype.ext hg)
  have h3 : (((LT l).PD K).actB g).toAlgHom.toLinearMap.restrictScalars ℚ_[l] =
      (((LT l).PD (levelField K s)).actB g').toAlgHom.toLinearMap.restrictScalars ℚ_[l] :=
    LinearMap.ext fun b => (((LT l).PD_actB K g b).trans (by rw [hg])).trans
      ((LT l).PD_actB (levelField K s) g' b).symm
  unfold actVB
  rw [h2, h3]

theorem iInf_eq_of {α β γ : Type} [CompleteLattice γ] (f : α → γ) (g : β → γ)
    (h1 : ∀ a, ∃ b, f a = g b) (h2 : ∀ b, ∃ a, f a = g b) : ⨅ a, f a = ⨅ b, g b :=
  le_antisymm (le_iInf fun b => by obtain ⟨a, ha⟩ := h2 b; exact ha ▸ iInf_le f a)
    (le_iInf fun a => by obtain ⟨b, hb⟩ := h1 a; exact hb ▸ iInf_le g b)

theorem finrank_congr {R M : Type} [Field R] [AddCommGroup M] [Module R M] {X X' : Submodule R M}
    (e : X = X') : Module.finrank R ↥X = Module.finrank R ↥X' := by rw [e]

theorem fixed_eq (Y : Lat K LL) : (⨅ g : ((HW l).W K s LL h).GKs,
      LinearMap.ker (actVB ((LT l).PD K) Y.ρ (g : ↥(GK K)) - LinearMap.id)) =
      Dcris ((LT l).PD (levelField K s)) (resKs h Y) := by
  refine iInf_eq_of _ _ (fun g => ?_) fun g' => ?_
  · have hg : (g.1.1 : GQ l) ∈ GK (levelField K s) := (mem_GKs ((HW l).W_s K s LL h) g.1).mp g.2
    exact ⟨⟨g.1.1, hg⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y g.1 ⟨g.1.1, hg⟩ rfl)⟩
  · exact ⟨⟨⟨g'.1, GK_le (K := K) (K' := levelField K s) h.2.2.1 g'.2⟩,
      (mem_GKs ((HW l).W_s K s LL h) _).mpr g'.2⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y _ _ rfl)⟩

theorem crys_iff (Y : Lat K LL) :
    IsCrysOn (sit LT HW l AI K s LL h) (sit LT HW l AI K s LL h).W.GKs Y ↔
      IsCrys ((LT l).PD (levelField K s)) (resKs h Y) := by
  have h1 := finrank_congr (fixed_eq LT HW h Y)
  have h2 := congrArg (· * Module.finrank ↥LL.1 Y.V) (finrank_maxUnramified_levelFieldFiniteExtension K s h.1).symm
  exact iff_of_eq (congrArg₂ Eq h1 h2)

end Hyp



variable {l : ℕ} [Fact l.Prime]

variable (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

variable (D : Formalism.BasicNotions.D7) (H : HWOf D.loc) (F : FonOf D.loc D.locA H)


end GlobalTheory.TorsionBoundCompare
