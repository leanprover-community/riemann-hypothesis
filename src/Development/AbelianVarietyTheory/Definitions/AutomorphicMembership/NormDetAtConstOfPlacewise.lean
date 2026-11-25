module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
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

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal

namespace GlobalTheory.ShFam.Pad

def inclQb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) : c.F →+* Qb :=
  c.F.val.toRingHom.codRestrict (algebraicClosure ℚ ℂ) fun a =>
    haveI := c.fin
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom c.F.val)


open Classical in
def carry {F : Type} [Field F] (f g : F →+* Qb) : Qb →+* Qb :=
  haveI : Nonempty (Qb →+* Qb) := ⟨RingHom.id Qb⟩
  if f = g then RingHom.id Qb else Classical.epsilon fun σ => σ.comp f = g

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

def ioAt (p : ℕ) [Fact p.Prime] (y : Pt s) : Qb →+* ℂ_[p] := (iotaP p).comp (carry y.fK (inclQb κ.c))

def normDetIo (p : ℕ) [Fact p.Prime] (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (io : Qb →+* ℂ_[p]) (a : Qb) : ℝ :=
  ‖io a‖ * Real.exp (∑ i : Fin N, y.lnRoot io p b (DV.tauEmb D τ) i)


open Classical in
def normDetAt (p : ℕ) (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (a : Qb) : ℝ :=
  if h : p.Prime then (haveI := Fact.mk h; normDetIo s p b τ y (ioAt s p y) a) else 1

def padAt {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
    (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s)
    (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp) : PadPkg D N j s.Comp jC ng :=
  { padOf s L G M F I with
    normDetT := fun p τ (y : Pt s) => normDetAt s p true τ y (F.sv τ y)
    normDetH := fun p τ (y : Pt s) => normDetAt s p false τ y (F.sv τ y) }

section Unfold

variable {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
  (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s) (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp)

end Unfold

end GlobalTheory.ShFam.Pad
