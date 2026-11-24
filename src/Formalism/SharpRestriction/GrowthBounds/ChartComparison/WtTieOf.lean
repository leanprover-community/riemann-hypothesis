module

public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CompFintype
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G.Cmp

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def FillTie (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w hg)) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (b : ℕ) (hb : b < D.R.m),
    ((Fl.w v (b + 1) s : ℤ) : ℚ) = wG D.R ((D.hcW u (Gt.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩) (b + 1)

theorem rk_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (j : ℕ) : (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1) := by
  have hk := Gt.gat_k u w hg
  show (D.gat u w hg).P.m + (j + 1) * (Fl.t + 1) + 1 = D.R.k + (j + 1) * (D.R.t + 1)
  rw [ht]
  omega

theorem wtTie_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w hg Fl) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (rk : (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1)) :
    WtTie (Fl.Pj (j + 1)) rk (Gt.gat_pos u w hg) (M.lam (j + 1)) := by
  intro (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) i
  have hk := Gt.gat_k u w hg
  show liftWt Fl.t (D.gat u w hg).P.m ((D.gat u w hg).P.lam0 v s) (fun a => Fl.w v a s) (j + 1) i =
    (M.lam (j + 1) (Gt.gat_pos u w hg ⟨v, s⟩)).w (finCongr rk i)
  apply Int.cast_injective (α := ℚ)
  rw [M.lam_eq (j + 1) hj (Gt.gat_pos u w hg ⟨v, s⟩) (finCongr rk i)]
  have hi : ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) = i.val := rfl
  unfold liftWt
  by_cases h1 : i.val < (D.gat u w hg).P.m + 1
  · have h2 : ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) < D.R.k := by rw [hi, ← hk]; exact h1
    rw [dif_pos h1, dif_pos h2, Gt.gat_lam u w hg v s ⟨i.val, h1⟩, (D.fm u).lam_eq 0 (Nat.zero_le _) _ _]
    exact dif_pos h2
  · have h2 : ¬ ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) < D.R.k := by rw [hi, ← hk]; exact h1
    rw [dite_eq_right h1, dite_eq_right h2, Int.cast_neg]
    congr 1
    have e1 : (i.val - ((D.gat u w hg).P.m + 1)) / (Fl.t + 1) =
        (((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) - D.R.k) / (D.R.t + 1) := by rw [hk, ht, hi]
    rw [e1]
    exact hF v s _ (D.R.blk_lt hj (finCongr rk i) h2)


variable {M} in
theorem StepIn.wt_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Fl : Fills (D.gat u w hg)} (Lv : Levels Fl) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w hg Fl) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (S : StepIn M (j + 1) hj (gatJ Lv (j + 1))) (hpos : S.pos = Gt.gat_pos u w hg) (β : S.Ch) :
    WtTie (gatJ Lv (j + 1)).P (S.loc β).rk S.pos (M.lam (j + 1)) := by
  rw [hpos]
  exact wtTie_of M Gt w hg Fl ht hF j hj _

end Formalism.MainNotions.G.CmpJ

end
