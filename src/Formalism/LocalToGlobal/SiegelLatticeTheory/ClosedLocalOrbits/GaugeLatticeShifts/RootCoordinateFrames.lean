module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal
open Matrix

namespace Formalism.L2.SG.RealObj.RootCoordinateFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NRealize : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ),
    (∀ a b, hJ ε (e a) (e b) = 0) → (∀ a b, hJ ε (f a) (f b) = 0) →
    (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) → hJ ε z z ≠ 0 →
    ∀ P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsLoUni P →
      ∃ s : Formalism.REAL.UJ ε, InN ε e z (uMat s) ∧ ∀ a, uMat s *ᵥ fam e z a = ∑ c, P a c • fam e z c

def RootCoordFrame : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ),
    (∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) → (∀ a, hJ ε (f a) z = 0) →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
      (∀ a, g *ᵥ fam e z a = ∑ c, P a c • fam e z c) →
      ∀ a : Fin r, rootCoord ε e f z g a = P a.succ a.castSucc

def TraceSum : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g : ℕ) (x : X.B.I.E),
    ∏ v, Complex.exp (2 * Real.pi * Complex.I * ((X.B.I.φ v x + star (X.B.I.φ v x)) / (g : ℂ))) =
      Formalism.L2.SG.PairVal.psiInf g (X.ιE x)

def ZhatNAct : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (s si s' g : Matrix (Fin n) (Fin n) ℂ)
    (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
    si * s = 1 → (∀ x y, hJ ε (s *ᵥ x) (s *ᵥ y) = hJ ε x y) →
    (∀ a, s *ᵥ f a = ∑ c, P a c • f c) → (∀ b, s' *ᵥ f' b = ∑ c, P' b c • f' c) →
    Zhat ε f f' (si * g * s') = P.map star * Zhat ε f f' g * P'.transpose

def FrameAtV : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0) ∧
    (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 ∧
      hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0) ∧
    hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw u : ℂ) ∧ Tw u ≠ 0

end Formalism.L2.SG.RealObj.RootCoordinateFrames
