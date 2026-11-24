module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpM
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

def alP (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z'

def beM (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (t : Fin (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ (t : ℕ)) * z' (wI k r t)

def RInvAlphaP : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (w m : B.Mat k r), inWb k r z' → w ∈ UWset k r z' → m ∈ Nset k r →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M),
      ∑ c ∈ jSetR k r, (∑ i : Fin (k + 1), alP k r z' i * ((m * w)⁻¹.submatrix c (rowsR k r i)).det) • X c =
        ((m * w)⁻¹).det • ∑ i : Fin (k + 1), alP k r z' i • X (rowsR k r i)

def RInvBetaP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g S : B.Mat k r), g ∈ B.GV k r → S ∈ B.GV k r →
    ∀ d : Fin (r + k) → Fin (2 * r + k + 1),
      ∑ J ∈ jSetR k r, beJ k r z g J * (S.submatrix J d).det = S.det * beJ k r z (g * S) d

def RInvBetaLeftP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h m g : B.Mat k r), inWb k r z → h ∈ UWset k r z → m ∈ Nset k r →
    g ∈ B.GV k r → ∀ J : Fin (r + k) → Fin (2 * r + k + 1), beJ k r z (h⁻¹ * m⁻¹ * g) J = beJ k r z g J

def RInvAlphaM : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g S : B.Mat k r), g ∈ B.GV k r → S ∈ B.GV k r →
    ∀ c : Fin (r + k) → Fin (2 * r + k + 1),
      ∑ J ∈ jSetR k r, alJ k r z g J * ((S⁻¹).submatrix c J).det = (S⁻¹).det * alJ k r z (g * S) c

def RInvAlphaLeftM : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h m g : B.Mat k r), inWb k r z → h ∈ UWset k r z → m ∈ Nset k r →
    g ∈ B.GV k r → ∀ J : Fin (r + k) → Fin (2 * r + k + 1), alJ k r z (h⁻¹ * m⁻¹ * g) J = alJ k r z g J

def RInvBetaM : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (w m : B.Mat k r), inWb k r z' → w ∈ UWset k r z' → m ∈ Nset k r →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M),
      ∑ d ∈ jSetR k r, (∑ t : Fin (k + 1), beM k r z' t * ((m * w).submatrix (colsV k r t) d).det) • X d =
        (m * w).det • ∑ t : Fin (k + 1), beM k r z' t • X (colsV k r t)

end

end Formalism.FourierDecayAlt.P.CutMP
