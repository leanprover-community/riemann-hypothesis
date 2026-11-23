module

public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

section Dat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

structure FamIn3 (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 I0 Ty T : Type) (m : ℕ) where

  A : FamIn K G Pl0 T m

  okI : T → Set I0

  heckeRI : ∀ τ, okI τ × Ty → Module.End K (A.MtildeCSD τ).Forms

  heckeLI : ∀ j τ, okI τ × Ty → Module.End K (A.MtCSD j τ).Forms

  trI : Fin m → (I0 × Ty → K) → I0 × Ty → K

namespace FamIn3

variable {I0 Ty T : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m)

def rowI (τ : T) : InertDat3 (A3.A.fam.R τ) I0 Ty where
  PlI := A3.okI τ
  plI := Subtype.val
  opI := A3.heckeRI τ

def liftI (j : Fin m) (τ : T) : InertDat3 (A3.A.fam.L j τ) I0 Ty where
  PlI := A3.okI τ
  plI := Subtype.val
  opI := A3.heckeLI j τ

def fam3 : DefFam3 K G Pl0 I0 Ty T (Fin m) where
  F := A3.A.fam
  RI := A3.rowI
  LI := A3.liftI
  trI := A3.trI

def side3 (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3) : DefSide A3.fam3.base3 := A3.fam3.side3 P ψ Zs

end FamIn3

end Dat

end Formalism.L2.DIV
