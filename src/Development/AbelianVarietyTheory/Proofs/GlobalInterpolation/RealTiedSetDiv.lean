module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField

namespace GlobalTheory.Fc

theorem realTied_setDiv {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (H : Formalism.L2.Theta.RealTied D) : Formalism.L2.Theta.RealTied (setDiv D N h) :=
  ⟨H.cdScale, H.dsig, H.dsig_all, H.vol⟩

theorem built_val (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd) (κ : Par) (D : D7) (O : Obj D) (c : ℝ) (b : Bd D O c)
    (hb : Built Q Lk κ D O c b) :
    Val κ.C κ.cD κ.ch O.L ∧ CanonInst O.Gx ∧ O.K = κ.C.GK ∧ O.cX = κ.C.cX ∧ O.L.sc.eps = κ.eps ∧
      (∀ u, D.div.h u = DV.hExpl6 D O.L O.X κ.C.Csz u) ∧ Nonempty (Formalism.L2.Theta.RealTied D) ∧
      Nonempty {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)} := by
  refine Built.ind (R := fun D O _ _ => Val κ.C κ.cD κ.ch O.L ∧ CanonInst O.Gx ∧ O.K = κ.C.GK ∧ O.cX = κ.C.cX ∧
      O.L.sc.eps = κ.eps ∧ (∀ u, D.div.h u = DV.hExpl6 D O.L O.X κ.C.Csz u) ∧ Nonempty (Formalism.L2.Theta.RealTied D) ∧
      Nonempty {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}) ?_ hb
  intro K β _ _ h0 _ _
  obtain ⟨h1, h2, h3, h4, -⟩ := h0
  rw [← h1, ← h2, ← h3, ← h4]
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact ⟨hv, β.p.pt_canon β.canon, rfl, rfl, congrArg Scale.eps β.sc, β.p.pt.xa.h_eq,
    ⟨realTied_setDiv _ _ β.c.real⟩, ⟨⟨(_, _), hv.Del_eq, hv.eta_eq⟩⟩⟩

end GlobalTheory.Fc
