module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcIotaInj
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem nc_capU (j : ℕ) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (k : ℕ) :
    Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) k =
      nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s k) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.capU nc_zc
  rw [nc_partner hg]
  have key : ∀ a : ℕ, t0 + a • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) + k • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
      t0 + ((a + k) % (D.gat u w hg).P.n' (Y.vOf u w hg t0)) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) := by
    intro a
    rw [hn, mod_addOrderOf_nsmul, add_nsmul, add_assoc]
  exact congrArg (fun t => Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t) + Formalism.MainNotions.G.cG L) (key s.val)

open Classical in
include hL ht0 in
theorem nc_gU_eq (K : Formalism.MainNotions.G.Consts) (j : ℕ) :
    Formalism.MainNotions.G.gU X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0 =
      Formalism.MainNotions.FormalGroupSystem.gam (D.what₂.places.resChar w) * ∑ s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0), nc_ya X Y u w hg t0 s -
        ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos, ∑' e : ℕ,
          min (nc_ya X Y u w hg t0 s / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (2 * e + 1))
            (nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1))) -
        Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0 := by
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.gU
  rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.sum_image (fun a _ b _ h => hinj h), Finset.filter_image,
    Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf]
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  rw [nc_tsum_odd]
  apply tsum_congr
  intro e
  rw [nc_capU X Y hT hL u w hg t0 ht0]
  rfl

include hL ht0 in
theorem growth_exclusion_sum_eq (K : Formalism.MainNotions.G.Consts) (j : ℕ) :
    Formalism.MainNotions.G.g0 X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0 =
      ∑ s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0), ∑' e : ℕ,
        (if Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w)
            (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) (2 * e + 1) then 0 else
          max 0 (nc_ya X Y u w hg t0 s / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (2 * e + 1) -
            nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) -
        Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0 := by
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.g0
  rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.sum_image (fun a _ b _ h => hinj h)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have e1 : ∀ e : ℕ, (if Odd e ∧ ¬ Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e then
        max 0 (Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (nc_iota Y u w hg t0 s) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ e -
          Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) e) else 0) =
      (if Odd e then (if Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e then 0 else
        max 0 (Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (nc_iota Y u w hg t0 s) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ e -
          Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) e)) else 0) := by
    intro e
    by_cases h1 : Odd e <;> by_cases h2 : Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e <;>
      simp [h1, h2]
  rw [tsum_congr e1, nc_tsum_odd]
  apply tsum_congr
  intro e
  rw [nc_capU X Y hT hL u w hg t0 ht0]
  rfl

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
