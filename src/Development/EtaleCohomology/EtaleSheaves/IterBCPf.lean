module

public import Development.EtaleCohomology.EtaleSheaves.ChowLCut
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterBCPf

theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} {a : P' ⟶ P} {q' : P' ⟶ X} {g : X ⟶ S}, IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' a q' g w
    exact IterLine.iso _ (w.isIso_snd_of_isIso he)
  | comp l k hl hk ih =>
    intro X P' a q' g w
    have hb : IsPullback (pullback.fst k g) (pullback.snd k g) k g := IsPullback.of_hasPullback k g
    let m : P' ⟶ pullback k g := pullback.lift (a ≫ l) q' (by rw [Category.assoc]; exact w.w)
    have hm : q' = m ≫ pullback.snd k g := (pullback.lift_snd _ _ _).symm
    have ht : IsPullback a m l (pullback.fst k g) := by
      refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm hb
      rw [← hm]; exact w
    rw [hm]
    exact IterLine.comp m _ (IsLine.bc hl ht) (ih hb)

theorem IterBC_of : IterBC := by
  intro P S X q g hq
  exact iterLine_of_isPullback hq (IsPullback.of_hasPullback g q).flip

end LateralTheory.E.IterBCPf

end
