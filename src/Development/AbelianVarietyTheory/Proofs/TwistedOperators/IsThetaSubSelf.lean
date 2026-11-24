module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CoinvKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def IsStabW (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  N ≤ A ∧ (∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N) ∧
    (∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N) ∧
    ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def HasRelY (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  (∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ A, om (g, 1) Φ - Φ ∈ N) ∧
    (∀ k ∈ KInf σ Y emb, ∀ Φ ∈ A, om (k, 1) Φ - Φ ∈ N) ∧
    ∀ γ ∈ Lines σ Y, ∀ Φ ∈ A, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def IsThetaSub (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  IsStabW om emb A N ∧ HasRelY om emb A N

end GlobalTheory.CoinvKer

end
