module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def blkHom (n r : ℕ) : Matrix (Fin n) (Fin n) k →* Matrix (Fin n ⊕ Fin r) (Fin n ⊕ Fin r) k where
  toFun A := fromBlocks A 0 0 1
  map_one' := by rw [← fromBlocks_one]
  map_mul' A B := by rw [fromBlocks_multiply]; simp


variable (k) in
def blkGL (n r : ℕ) : GL (Fin n) k →* GL (Fin (n + r)) k :=
  Units.map ((reindexAlgEquiv k k finSumFinEquiv).toMonoidHom.comp (blkHom k n r))


variable (k) in
def glCongr {a b : ℕ} (h : a = b) : GL (Fin a) k →* GL (Fin b) k :=
  Units.map (reindexAlgEquiv k k (finCongr h)).toMonoidHom


variable (k) in
def blkAt (n N : ℕ) (h : n ≤ N) : GL (Fin n) k →* GL (Fin N) k :=
  (glCongr k (Nat.add_sub_cancel' h)).comp (blkGL k n (N - n))

def IsPsd {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ ∀ v, 0 ≤ (B v v).re


variable (k) in
def lvlChar (ψ : AddChar k Circle) (N n : ℕ) : derUnip k N n →* ℂˣ :=
  (whitCharFrom k ψ N (n - 1)).comp (Subgroup.inclusion (derUnip_le_unipB k N n))

def Kills {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V)
    (n : ℕ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ v ∈ twKer π (derUnip k N n) (lvlChar k ψ N n), ∀ w, B v w = 0

def MirEq {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (m : ℕ) (h : m + 1 ≤ N)
    (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ p ∈ Mir k m, ∀ v w, B (π (blkAt k (m + 1) N h p) v) (π (blkAt k (m + 1) N h p) w) =
    ((nabs k (Matrix.GeneralLinearGroup.det p) ^ s : ℝ) : ℂ) * B v w


variable (k) in
def scalAt (n N : ℕ) (h : n ≤ N) (z : kˣ) : GL (Fin N) k :=
  blkAt k n N h (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom z)

end PositivityTheory.RgUd.Form
