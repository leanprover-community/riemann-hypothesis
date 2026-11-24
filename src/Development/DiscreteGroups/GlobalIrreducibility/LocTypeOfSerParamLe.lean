module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
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

namespace DiscreteGroups.sglob.DzType.Rt

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.SerSys
open scoped Classical

attribute [local instance] GlobalTheory.SerSys.factTypePrime

variable {g : ℕ} [Fact g.Prime]

def SerParamLe (b : ℕ) (e : ∀ n : ℕ, (ZMod g)[X] → MonoidAlgebra ℂ (Gn g n)) (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ine : ∀ n, QRep g n → ℂ[X]) : Prop :=
  ∀ n, n ≤ b → ∀ (π : QRep g n), IrrSm π → ∀ f, (∃ v ∈ fixK1 π.ρ, actK π.ρ (e n f) v ≠ 0) →
    ine n π = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod

def LabParamLe (b : ℕ) (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) : Prop :=
  ∀ k v, SerParamLe b (eSerC (L k)) (L k).teich fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)

theorem one_le_nV (D : D7) : 1 ≤ D.R.nV := by
  have ht : 0 < D.R.t := D.R.t_odd.pos
  unfold Formalism.BasicNotions.Ranks.nV
  omega

theorem r_le_nV (D : D7) : D.R.r ≤ D.R.nV := by
  unfold Formalism.BasicNotions.Ranks.nV
  omega

end DiscreteGroups.sglob.DzType.Rt

end
