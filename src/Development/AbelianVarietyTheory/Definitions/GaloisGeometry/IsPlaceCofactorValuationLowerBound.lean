module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
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

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

def SiteAdm (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w hg)) (Lv : Levels Fl) (Ch : Chain Lv) : Prop :=
  ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : ℕ → ℕ)
    (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) Fl Lv Ch std vp unif eO eO_spec dG dG_spec om)),
    FormalGroupSystem.admitted D _ Y5 ∧ dG 0 = 0 ∧ ∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam

def phAt {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) :
    MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p) :=
  ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
    sub2 p be (MvPowerSeries.X (Sum.inl ⟨v, e⟩)) (MvPowerSeries.X (Sum.inr ⟨v, e⟩))

def IsPlaceCofactorValuationLowerBound {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) (g : ℝ) : Prop :=
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p), IntS p (inParam p U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), ∃ a : WW p,
      AddMonoidAlgebra.coeff (applyD (X.PIv j I v) (X.ThZA (K0 p) j (expS p (-phAt X be j v) * U))) n =
        (p : K0 p) ^ ⌈g⌉ * algebraMap (WW p) (K0 p) a

def inE {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) :
    Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕ Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) →
      X.EA j ⊕ X.EA j :=
  Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j))

def thOne {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (K0 p))
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p)) : MvPowerSeries (Zidx n' r0 r1) (K0 p) :=
  ThZ B (K0 p) 1 (expS p (-(∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)))) * U)

def toFin {n : ℕ} [NeZero n] (s : ZMod n) : Fin n := ⟨s.val, ZMod.val_lt s⟩

def inLetters {n r0 r1 : ℕ} [NeZero n] {R : Type} [Semiring R] (f : MvPowerSeries (Zidx n r0 r1) R) :
    MvPowerSeries (ZMod n × Fin r0 × Fin r1) R :=
  resV (fun x => (toFin x.1, x.2)) f

end GlobalTheory.TwU

end
