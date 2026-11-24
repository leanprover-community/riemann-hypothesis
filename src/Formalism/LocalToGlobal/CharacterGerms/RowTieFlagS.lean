module

public import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Flag

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {m : ZMod d → ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

def idxS (hd : ZMod d) (g : Fin 2) (t : ZMod d) : ZMod d := if g = 0 then t else t - hd

theorem rkF_sigmaS (hd : ZMod d) (X : RowData C V d (fun _ => Σ a : ZMod d, Fin (m a)) J)
    (hty : ∀ (g : Fin 2) (x : Σ a : ZMod d, Fin (m a)), (X.G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd)
    (g : Fin 2) (t : ZMod d) : X.rkF g t = m (idxS hd g t) := by
  unfold RowData.rkF
  refine Finset.card_eq_of_equiv_fin
    ((Equiv.subtypeEquivRight fun c => ?_).trans (Equiv.sigmaSubtype (idxS hd g t)))
  rw [Finset.mem_filter, hty]
  simp only [Finset.mem_univ, true_and]
  unfold idxS
  by_cases hg : g = 0
  · simp only [if_pos hg]
  · simp only [if_neg hg]
    exact eq_sub_iff_add_eq.symm

def stdFlagS (hd : ZMod d) (X : RowData C V d (fun _ => Σ a : ZMod d, Fin (m a)) J)
    (hty : ∀ (g : Fin 2) (x : Σ a : ZMod d, Fin (m a)), (X.G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd) :
    Flag X where
  en := fun g t q => ⟨idxS hd g t, ⟨q.val, (rkF_sigmaS hd X hty g t) ▸ q.isLt⟩⟩
  en_inj := fun g t q q' h => by
    have h1 := eq_of_heq (Sigma.mk.inj h).2
    exact Fin.ext (Fin.mk.inj_iff.1 h1)
  en_ty := fun g t q => by
    rw [hty]
    unfold idxS
    by_cases hg : g = 0
    · simp [hg]
    · simp [hg]

end Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

end Formalism.L2.FormalSeriesBounds
