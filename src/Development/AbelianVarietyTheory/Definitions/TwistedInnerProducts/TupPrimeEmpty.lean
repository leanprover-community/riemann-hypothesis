module

public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def tupPrime {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T0) : ℕ :=
  ∏ q ∈ (R.Q t).image (fun PP => Nat.card (kP PP)), q

def XiVal {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ t x, ((R.xi t x : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange

def RatG {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (ph : Fin D.R.m → ℂ) : Prop :=
  ∀ (i : Fin D.R.m) (t : T0) (x : A.fam.amb.FL i t), ∃ y : Fin (R.nW i) → D.what₂.LL,
    (R.FW i).j (sg0 D A) y = ph i • R.thG i t (R.jV i t x)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

def CoverField : Prop :=
  ∀ (i : Fin D.R.m) (t : T0) (l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H), T.Q.l.Dvd l₂ → l₂.M = T.Q.l.M * tupPrime R t → l₂.A = 1 →
    ∀ (Xo₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (T.Q.Dw ((i : ℕ) + 1)) l₂) (c₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₂),
      c₂.F = D.what₂.embLL.toRatAlgHom.fieldRange → FnAlgClosed (Xo := Xo₂) (c := c₂)

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def PinsOverL (i : Fin D.R.m) : Prop :=
  ∃ O' : OMDat T.toCore R i T0 id, O'.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

def OneMapOverL (ph : ℂ) (i : Fin D.R.m) : Prop :=
  ∃ O' : OMDat T.toCore R i T0 id, O'.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧
      O'.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O'.s0) ph

end GlobalTheory.TwistField
