module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBSelfAdj
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CommuteEPderiv
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem inl_ne {N r t : ℕ} (a b : ℕ) (ha : a < N) (hb : b < N) (hab : a ≠ b) (c c' : Fin r) :
    (Sum.inl (Formalism.GM.M.finPos N a, c) : Formalism.GM.M.BVar N r t) ≠ Sum.inl (Formalism.GM.M.finPos N b, c') := by
  intro h
  have h2 := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1
  simp only [Formalism.GM.M.finPos] at h2
  rw [min_eq_left ha.le, min_eq_left hb.le] at h2
  exact hab h2

theorem commCondition : RestTieComm := by
  intro p _ N r _ G hG j jp i i' hii' x
  obtain ⟨⟨hmono, hvec, -⟩, hlt, -, -⟩ := hG
  have hpN : ∀ k, G.T.pos k + 1 < N := fun k => (hlt k).trans G.uPos.isLt
  have hne : G.T.pos i ≠ G.T.pos i' := hmono.injective.ne hii'
  have hcross : ∀ a b : Fin G.T.t, G.T.pos a + 1 ≠ G.T.pos b := by
    intro a b hab
    obtain ⟨ha, -, ha2⟩ := hvec a
    obtain ⟨hb, hb1, -⟩ := hvec b
    have e : G.LL.vec ⟨G.T.pos a + 1, ha⟩ = G.LL.vec ⟨G.T.pos b, by omega⟩ :=
      congrArg G.LL.vec (Fin.ext hab)
    rw [e] at ha2
    exact absurd (hb1.symm.trans ha2) (by decide)
  exact commute_tiePhi _ _ _ _
    (fun c c' => inl_ne _ _ (by have := hpN i; omega) (by have := hpN i'; omega) hne c c')
    (fun c c' => inl_ne _ _ (hpN i) (by have := hpN i'; omega) (hcross i i') c c')
    (fun c c' => inl_ne _ _ (by have := hpN i; omega) (hpN i') (hcross i' i).symm c c')
    (fun c c' => inl_ne _ _ (hpN i) (hpN i') (fun h => hne (by omega)) c c')
    _ _ _ _ _ _ x

theorem symmCondition (C0 CE1 CE2 : ℝ) (X : Formalism.MainNotions.flipOneThree.Inst) : RestSymm C0 CE1 CE2 X :=
  restSymm_of commCondition C0 CE1 CE2 X

end Formalism.MainNotions.G.SymmetricFormBlocks

end
