module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

def spAct {R : Type} [CommRing R] [Algebra F R] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    (κ → R) × (κ → R) :=
  (fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inl k),
    fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inr k))

def weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 0 1 (-1) 0

def leviM (A : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks A 0 0 A⁻¹ᵀ

def unipM (S : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 1 0 S 1

def IsSymp (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop := G.transpose * weylM * G = weylM

def gens : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {G | ∃ A : Matrix κ κ F, IsUnit A.det ∧ G = leviM A} ∪ {G | ∃ S : Matrix κ κ F, S.transpose = S ∧ G = unipM S} ∪ {weylM}

variable [NumberField F]

def indO (v : Pl (F := F)) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def HasOp (ψ : AddChar (AF F) ℂ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    Function.Surjective ei ∧ (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧
    (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ)) ∧
    (∀ v, (SB _).map (ev v) = SB _) ∧ (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (spAct G w) (ev v φ)) ∧
    (∀ᶠ v in cofinite, ev v (indO v) = indO v) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)

end GlobalTheory.SympChange
