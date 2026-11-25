module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitLoc
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
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

namespace PositivityTheory.ThK.SplitDict

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip
open PositivityTheory.KCo PositivityTheory.ThK.SplitLoc GlobalTheory.SplitWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def intInd {m n : ℕ} (v : Pl F) : Matrix (Fin m) (Fin n) (Fv F v) → ℂ :=
  Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1

def DictAt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (v : Pl F)
    (τ : E →ₐ[F] Fv F v) : Prop :=
  ∃ (b : GL (Fin a) (Fv F v)) (b' : GL (Fin a') (Fv F v)) (c : GL (Fin (a + a')) (Fv F v))
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ))
    (ι' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
    (gl : UA σ G.V.J → GL (Fin a) (Fv F v)) (gl' : UA σ G.V'.J → GL (Fin a') (Fv F v))
    (hl : UA σ G.W.J → GL (Fin (a + a')) (Fv F v)),
    G.M.IsLinW B.ψ τ b c ι ∧ G.M'.IsLinBar B.ψ τ b' c ι' ∧
    (∀ hv : v ∈ B.P, τ = B.τ ⟨v, hv⟩ → b = G.V.bas v ∧ b' = G.V'.bas v ∧ c = G.W.bas v) ∧
    ι (G.M.vac v) = intInd v ∧ ι' (G.M'.vac v) = intInd v ∧
    (∀ g ∈ UAt σ G.V (evFin F v), Reads v ι (om (g, 1)) (omA (chrW X.ν τ) (chrW X.β τ) (gl g) 1)) ∧
    (∀ h ∈ UAt σ G.W (evFin F v), Reads v ι (om (1, h)) (omA (chrW X.ν τ) (chrW X.β τ) 1 (hl h))) ∧
    (∀ g ∈ UAt σ G.V' (evFin F v), Reads v ι' (om' (g, 1)) (omB (chrW X.ν τ) (chrW X.α τ) (gl' g) 1)) ∧
    (∀ h ∈ UAt σ G.W (evFin F v), Reads v ι' (om' (1, h)) (omB (chrW X.ν τ) (chrW X.α τ) 1 (hl h))) ∧
    (∀ x, ∃ h ∈ UAt σ G.W (evFin F v), hl h = x)

def Dict : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ (v : Pl F) (τ : E →ₐ[F] Fv F v),
      DictAt B G X om om' v τ

def IndIwasawa : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ)
    (α β : kˣ →* ℂˣ), ∀ F ∈ indSp a a' α β, (∀ h ∈ GlobalTheory.SplitWeil.KO k (Fin (a + a')), F h = 0) → F = 0

def RamNonzero : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (a a' : ℕ) (ϖ : kˣ) (α β ν : kˣ →* ℂˣ), HidaSetting a a' ϖ α β ν → ¬ IsUnram ν →
    ∃ Φ ∈ GlobalTheory.SplitWeil.SB _, pRam a a' ϖ ν β Φ ≠ 0

end PositivityTheory.ThK.SplitDict
