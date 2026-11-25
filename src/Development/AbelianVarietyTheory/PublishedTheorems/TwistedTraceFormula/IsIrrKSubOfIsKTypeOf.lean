module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix
open Formalism.REAL (Jm Kset inG)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsKTypeOf IsDS lowKSub UJset)
open Formalism.L2.Theta (SmoothVec dRep)

namespace GlobalTheory.KFinVec

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

theorem isKStableOn_kFinSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (kFinSub ε σ) := by
  rintro g hg v ⟨S, hS, hv, hK⟩
  exact ⟨S, hS, hK g hg v hv, hK⟩

def IsIrrKSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ IsKStableOn ε σ S ∧
    ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S

def IsKMapFrom (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (T : S →ₗ[ℂ] H) : Prop :=
  ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s)

def kIsotypic (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  ⨆ T : {T : S →ₗ[ℂ] H // IsKMapFrom ε σ S T}, LinearMap.range T.1

def IsAdmissible (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsIrrKSub ε σ S → FiniteDimensional ℂ (kIsotypic ε σ S)

def IsLieStable (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  ∀ X, inG ε X → ∀ v ∈ S, dRep σ X v ∈ S

end GlobalTheory.KFinVec

namespace GlobalTheory.Published

open GlobalTheory.KFinVec

def KFiniteVectorsUnitary : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    IsAdmissible ε σ ∧
    (∀ v : H, IsKFin ε σ v → AnalyticOnUJ ε fun g => σ g v) ∧
    Dense (kFinSub ε σ : Set H) ∧
    IsLieStable ε σ (kFinSub ε σ) ∧
    ∀ S : Submodule ℂ H, S ≤ kFinSub ε σ → IsLieStable ε σ S → S = ⊥ ∨ S = kFinSub ε σ

namespace KFiniteVectorsUnitary

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem analytic [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : AnalyticOnUJ ε fun g => σ g v := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, analyticOnNhd_const, fun _ _ _ => Subsingleton.elim _ _⟩
  · exact (h n ε H σ hU hI).2.1 v hv

theorem smoothOnH [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) :
    Formalism.QuantumDeterminants.SmoothOnH (Jm ε) fun g => σ g v :=
  (h.analytic hU hI hv).smoothOnH

theorem hasDerivAt [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by simp [UJset, Formalism.REAL.inUJ]
  have := ((h.analytic hU hI hv).analytic_exp h1 hX 0).differentiableAt
  simp only [Matrix.one_mul] at this
  exact this.hasDerivAt

theorem of_isDS (h : KFiniteVectorsUnitary) {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) :
    IsAdmissible ε σ ∧
    (∀ v : H, IsKFin ε σ v → AnalyticOnUJ ε fun g => σ g v) ∧
    Dense (kFinSub ε σ : Set H) ∧
    IsLieStable ε σ (kFinSub ε σ) ∧
    ∀ S : Submodule ℂ H, S ≤ kFinSub ε σ → IsLieStable ε σ S → S = ⊥ ∨ S = kFinSub ε σ :=
  haveI := hσ.1
  haveI := hσ.2.1
  h n ε H σ hσ.2.2.1 hσ.2.2.2.1

end KFiniteVectorsUnitary

end GlobalTheory.Published

end
