module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.HermitianCurvature.StatementMA
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def instCM (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

attribute [local instance] instCM

structure Parts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Type 1 where
  Wp : InfinitePlace D.host.E → Type
  Wq : InfinitePlace D.host.E → Type
  [pN : ∀ x, NormedAddCommGroup (Wp x)]
  [pI : ∀ x, InnerProductSpace ℂ (Wp x)]
  [qN : ∀ x, NormedAddCommGroup (Wq x)]
  [qI : ∀ x, InnerProductSpace ℂ (Wq x)]
  [pF : ∀ x, FiniteDimensional ℂ (Wp x)]
  [qF : ∀ x, FiniteDimensional ℂ (Wq x)]
  S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq
  T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j))
  f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))
  χ : ℝ → ℝ
  ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ
  m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r
  top : ∀ j : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) → List Formalism.FourierDecayAlt.C.Letter →
    Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ
  A₀ : ℝ
  τ : Fin S.f ≃ InfinitePlace X.B.I.F
  Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ
  Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ
  eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v
  eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v
  L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r
  j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
    Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT
  lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ
  c : Formalism.FourierDecayAlt.LE.Cut
  Cm : Fin S.f → ℝ
  σ : Fin S.f → ℝ
  Lw : ℕ → Fin S.f → ℝ
  Ll : ℕ → ℕ → Fin S.f → ℝ
  Ll' : ℕ → ℕ → Fin S.f → ℝ

attribute [instance] Parts.pN Parts.pI Parts.qN Parts.qI Parts.pF Parts.qF

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.Pins (P : Parts X u u') (CA : ℝ) (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ)
    (l : ℕ) : Prop :=
  P.S.CA = CA ∧ P.S.G = G0 ∧ P.S.de = de ∧ P.S.de' = de' ∧ P.S.l = l ∧ Formalism.L2.SG.DataInst.Compat P.S u u'

def Parts.Built (P : Parts X u u') : Prop := Formalism.FourierDecayAlt.D.IsBuilt P.S P.T P.f P.χ P.ν' P.m₀ P.top P.A₀

def Parts.FromX (P : Parts X u u') : Prop := BuiltFromX X P.S u u' P.T P.f P.τ P.Q P.Qi P.eP P.eQ

def Parts.Base (P : Parts X u u') (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  BaseFromX X P.S u u' i0 i0' P.τ P.Q P.Qi P.ν' P.m₀

end Formalism.L2.SG.Pf.Carrier
