module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

def KgMat (I : AutInst) (g : ℕ) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    Prop :=
  (∀ y, y ∈ I.Lf ↔ M *ᵥ y ∈ I.Lf) ∧
    ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (M - 1) *ᵥ y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • z

def InNInt (I : AutInst) (N : ℕ) (x : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) : Prop :=
  ∃ z ∈ Formalism.MainNotions.S.IntAf I.F I.E, x = (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * z

def EntriesLat : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ N : ℕ, 1 ≤ N ∧
    ∀ M M' : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), M * M' = 1 →
      (∀ i j, InNInt I N ((M - 1) i j)) → (∀ i j, InNInt I N ((M' - 1) i j)) → KgMat I g M

def FinNhdA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 1 ≤ N →
    {a : FiniteAdeleRing (𝓞 F) F | ∃ z ∈ Formalism.UG.intAd F, a = (N : FiniteAdeleRing (𝓞 F) F) * z} ∈
      𝓝 (0 : FiniteAdeleRing (𝓞 F) F)

def FinNhdB : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∀ U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z ∈ Formalism.UG.intAd F, (N : FiniteAdeleRing (𝓞 F) F) * z ∈ U

end PI.InvTopW
