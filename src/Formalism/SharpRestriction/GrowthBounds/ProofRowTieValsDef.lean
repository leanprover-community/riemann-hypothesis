module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

structure IsEndo (Y : FBChart C V O dd) (φ : Pt C 1 dd) : Prop where
  int : ∀ i, IntS V (φ i)
  cc : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0
  add : comp1 φ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
    addOf Y.B.G.F (comp1 φ (pt C (n := 2) dd 0)) (comp1 φ (pt C (n := 2) dd 1))

structure GmPack (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
    (γ γ' : Fin 2 → Fin 2 → Pt C 1 dd) : Prop where
  endo : ∀ r s, IsEndo Y (γ r s)
  endo' : ∀ r s, IsEndo Y (γ' r s)
  comm : ∀ r s a, comp1 (γ r s) (Y.B.A.act a) = comp1 (Y.B.A.act a) (γ r s)
  comm' : ∀ r s a, comp1 (γ' r s) (Y.B.A.act a) = comp1 (Y.B.A.act a) (γ' r s)
  lin : ∀ r s c, linAct (γ r s) (p.e c) = p.gm (p.ty0 c) r s • p.e c
  lin' : ∀ r s c, linAct (γ' r s) (p.e c) = p.gm (p.ty0 c + p.hd) r s • p.e c
  img : ∀ r s (v : Fin dd → C), ∃ b : I0 → C, linAct (γ r s) v = ∑ c, b c • p.e c
  img' : ∀ r s (v : Fin dd → C), ∃ b : I0 → C, linAct (γ' r s) v = ∑ c, b c • p.e c
  adj : ∀ r s, IntS V (FB.expS C (ev (n := 2) ![comp1 (γ r s) (pt C dd 0), pt C dd 1] Y.h -
    ev (n := 2) ![pt C dd 0, comp1 (γ' r s) (pt C dd 1)] Y.h))

def GmPackSt (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) : Prop :=
  ∃ γ γ' : Fin 2 → Fin 2 → Pt C 1 dd, GmPack Y p γ γ'

end Formalism.L2.FormalSeriesBounds
