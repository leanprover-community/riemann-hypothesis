module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaA
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure IsLatRepL {nS nT : ℕ} (σ : E →ₐ[F] E) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (hc : HeisClosedF σ JS JT ξ₀ ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)) : Prop where
  hw : w + sgOF σ w = 1
  sd : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)
  span : Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} = ⊤
  fin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0
  op : ∀ p x v, Om p (opFF hc w x v) = opFF hc w (rhoFF σ JS JT p x) (Om p v)
  sd' : ∀ p, SelfDual (gamFF σ JS JT ξ₀ ψ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p))
  vac : ∀ p e, Fixes (opFF hc w) (latF F E nS nT Λ) e →
    Om p e = normOp lam (opFF hc w) (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) e
  good : GoodNorm (sgOF σ) lam
  lev : ∀ x : XFF F E nS nT, ∃ N : ℕ, 0 < N ∧ ∀ l ∈ latF F E nS nT Λ,
    ψ (symplOHF σ JS JT ξ₀ (x : WOF F E nS nT) (N • (l : WOF F E nS nT))) = 1
  near : ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ
  near' : ∀ (x : XFF F E nS nT) (N : ℕ), 0 < N → ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT),
    ∃ l ∈ latF F E nS nT Λ, rhoFF σ JS JT p x = x + N • l
  splitStab : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ

end UpperTheory.TP.W

end
