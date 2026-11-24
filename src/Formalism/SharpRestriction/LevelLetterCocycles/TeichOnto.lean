module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
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

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing

def TeichOnto (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ a : ZMod p, a ≠ 0 → ∃ j : DeltaT p, PadicInt.toZMod (j.1 : ℤ_[p]) = a

def ComplMax : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ),
    (p : O) ∈ maximalIdeal O → (p : O) ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O →
      IsAdicComplete (maximalIdeal O) O

def zpEquiv {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : ℤ_[p] ≃+* ℤ_[q] := by
  subst h
  exact RingEquiv.refl _

def ιZrec {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    ℤ_[(P.PD K).p] →+* ↥(OL LL) :=
  (algebraMap ℤ_[l] ↥(OL LL)).comp (zpEquiv (P.PD_p K)).toRingHom

def UTieRec (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
    ∃ uZ : ℤ_[((D.loc l).PD K).p]ˣ, ((uZ : ℤ_[((D.loc l).PD K).p]) - 1).valuation = 1 ∧
      ιZrec (D.loc l) K LL uZ = (((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL))

end Formalism.MainNotions.N.Ln03
