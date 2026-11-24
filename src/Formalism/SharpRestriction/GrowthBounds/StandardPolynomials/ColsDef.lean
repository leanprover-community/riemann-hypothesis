module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCoreDef
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.YcondFactor
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

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

structure ColSys (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O) (mu : ℝ) (β : GlobalTheory X)
    (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) where
  ι : Type
  fin : Fintype ι
  Kc : ι → MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)
  dK : ι → Fin (2 * segS X.TT j + 1) → ℕ
  pl : ι → MonH X
  fC : ι → RHH O X
  oC : ι → ℕ
  dgC : ι → X.TT × Bool → ℕ
  a0 : ℕ
  KInt : ∀ a, Kc a ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)
  KPol : ∀ a, Kc a ∈ Pol (KK O) X.m (dK a)
  digit_le_one : ∀ a i, dK a i ≤ 1
  dKsum : ∀ i, ∑ a, dK a i = (L.LL j).deg i
  Kprod : ∏ a, Kc a = G
  facC : ∀ a, IsFac w (fC a) (oC a)
    (monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)))
  homC : ∀ a, HomW (ndHom X) (oC a)
    (monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)))
  fPol : ∀ a, fC a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC a)
  polC : ∀ a, monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC a)
  plQ : ∀ a l, multideg (pl a) l ≤ X.p ^ X.G'
  dgCQ : ∀ a l, dgC a l ≤ X.p ^ X.G'
  dgCY : ∀ a j', dgC a (topEnd X j', false) = 0
  a0le : (a0 : ℤ) + ∑ i : Fin (segS X.TT j), (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤
    (X.seg C0 CE1 CE2 j).A0 X.p
  plSum : ∑ a, pl a = Finsupp.single ((topStart X j, true), 0) ((X.seg C0 CE1 CE2 j).Qj X.p * a0) +
    ∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)))
  oSum : ∑ a, oC a = (∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
      (L.LL j).deg ⟨2 * (i : ℕ), by have := i.2; omega⟩) + (L.LL j).deg ⟨2 * segS X.TT j, by omega⟩

def ColsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (j : Fin (numSeg X.TT)) (y : Tx X.m (L.LL j)),
      y ∈ sAll (L.LL j) (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr →
      Nonempty (ColSys C0 CE1 CE2 X O S.w (mm + (n : ℝ) * ka1 X) β L j (psiR (KK O) (L.LL j) y))

def RestCols : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
