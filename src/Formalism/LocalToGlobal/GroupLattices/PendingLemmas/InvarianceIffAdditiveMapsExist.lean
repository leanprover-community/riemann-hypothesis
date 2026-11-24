module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SuccMulSuccSubOneDivSucc
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ConditionIffAdditiveMaps
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CardFilterValLt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

theorem oddDeg_of_vt (X : Sys p) (j : ℕ) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).Vtup) : OddDeg X j G := by
  classical
  intro m hm b hb
  obtain ⟨d, hd, hw⟩ := vtOddDeg X j G hG b.1 b.2 hb
  have h1 : Finsupp.weight (wBk X j b.1 b.2) m = d := hw (MvPolynomial.mem_support_iff.1 hm)
  rw [← hd, ← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold wBk blkJ
  by_cases hx : (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = b
  · have hx' : (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨b.1, b.2⟩ := hx
    rw [if_pos hx, if_pos hx']
    simp
  · have hx' : ¬ (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨b.1, b.2⟩ := hx
    rw [if_neg hx, if_neg hx']
    simp

def GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (G : (X.Pj j).Xsp) : Prop :=
  GoodG X Kc j G ∧ OddDeg X j G

theorem vtIn_GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] : VtIn X (GdC X Kc) :=
  fun j G hG => ⟨vtGood X Kc j G hG, oddDeg_of_vt X j G hG⟩

theorem delEquivOn_GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] :
    DelEquivOn X Kc (GdC X Kc) :=
  fun j A G f hG => (delEquivH X Kc j A G f hG.1 hG.2).2

structure CEmbC (G : GAtP p) extends CEmb G where
  rd : ∀ v, G.P.W v →+* WW p
  compat : Compat G toCEmb rd

variable (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

abbrev pendT : Pend X := pendR X E.toCEmb hfin hst (beLT hLT) (thFOf X pos F)

theorem invariance_iff_additive_maps_exist (D : Formalism.BasicNotions.D7) :
    Formalism.MainNotions.FormalGroupSystem.adm5 D X (pendT X E hfin hst hLT pos F) ↔
      ∀ v, ∀ j < X.mm, letI := algKfC E.toCEmb; XiEx X ℂ_[p] (pendT X E hfin hst hLT pos F).ThF v j :=
  condition_iff_additive_maps X E.toCEmb hfin hst (beLT hLT) _ _ _ D

end Formalism.L2.G.Pend
