module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitary
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace
open GlobalTheory.CoverModel GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

noncomputable section

namespace GlobalTheory.RealPar.CoverFactor

theorem signCompat_of_blockOrd {p q n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) :
    SignCompat ε e := by
  rintro (a | a)
  · simpa using h.1 a
  · simpa using h.2.1 a

theorem dictionary : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (U : URep T) (σ : Matrix (Fin n) (Fin n) ℂ → (U.H →L[ℂ] U.H)), BlockOrd e ε → Factors U e σ → IsURepOn (UJset ε) σ ∧ (IrrU U → IsIrredOn (UJset ε) σ) ∧ (∀ x, KFin T U.π x ↔ IsKFin ε σ x) ∧ (∀ Y, Y ∈ upq p q ↔ Formalism.REAL.inG ε (Matrix.reindex e e Y)) ∧ (∀ Y ∈ upq p q, ∀ t : ℝ, U.π (T.expt (t • Y)) = σ (NormedSpace.exp (t • Matrix.reindex e e Y))) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∃ x ∈ T.Kset, U.π x = σ k := by
  intro p q n e ε T U σ h hF
  have hφ : IsFormIso ε (plainMat e) := isFormIso_plainMat (signCompat_of_blockOrd h)
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have := hF 1
    rw [map_one, map_one] at this
    rw [this]
    simp
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := h.cov_surj T ha
    obtain ⟨y, rfl⟩ := h.cov_surj T hb
    have := hF (x * y)
    rw [map_mul, map_mul, hF x, hF y] at this
    rw [← ContinuousLinearMap.mul_def, this]
    simp [Matrix.submatrix_mul_equiv]
  · intro g hg v
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    rw [← hF x]
    exact U.isom x v
  · intro v
    refine CoverURep.continuousOn_of_cover h T _ ?_
    simpa only [← hF _] using U.cont v
  · intro hI S hS hst
    refine hI.2 S hS fun x v hv => ?_
    rw [hF x]
    exact hst _ (h.cov_mem T x) v hv
  · intro x
    have := kFin_iff (s := RingHom.id ℂ) hφ (T := T) (π := U.π) (σ := σ) (LinearIsometryEquiv.refl ℂ U.H)
      (c := fun _ => 1) (fun _ => one_ne_zero) (fun g y => by rw [one_smul, hF g]; rfl) x
    exact this.symm
  · intro Y
    exact (hφ.mem_lie Y).symm
  · intro Y hY t
    rw [hF, T.expt_cov _ (KStabLie.smul_mem_upq hY t)]
    exact congrArg σ (hφ.exp Y t).symm
  · intro k hk
    obtain ⟨x, hx⟩ := hφ.surj T (mem_K_iff.1 hk).1
    refine ⟨x, (hφ.mem_K T x).1 (hx ▸ hk), ?_⟩
    rw [hF x]
    exact congrArg σ hx

end GlobalTheory.RealPar.CoverFactor

end
