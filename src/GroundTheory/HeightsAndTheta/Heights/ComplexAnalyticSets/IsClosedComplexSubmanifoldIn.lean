module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Instances.Matrix
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
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Pointwise

variable {n d : ℕ}

def linPoly (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A (Pi.single j 1) i) * X j

def projAlgHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  aeval fun i => Ideal.Quotient.mk J (linPoly A i)

def IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) : Prop :=
  Function.Injective (projAlgHom J A) ∧ (projAlgHom J A).toRingHom.Finite

def unitaryRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {M | M * M.conjTranspose = 1}

def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    (∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
        (∃ M : Matrix (Fin d) (Fin n) ℂ, ∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) ∧
        ∀ M : Matrix (Fin d) (Fin n) ℂ,
          (∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) → IsFiniteProjection J M.mulVecLin) ∧
      (∃ M : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J M.mulVecLin) ∧
      (∀ D ⊆ unitaryRows d n, unitaryRows d n ⊆ closure D →
        ∃ M ∈ D, IsFiniteProjection J M.mulVecLin) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) ℂ),
        (∀ k, F k ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((U * F k).conjTranspose.submatrix s id).mulVecLin))

def lineMap : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval ![X 0, 0]

def lineIdeal : Ideal (MvPolynomial (Fin 2) ℂ) := RingHom.ker lineMap

theorem lineMap_surjective : Function.Surjective lineMap := by
  intro p
  refine ⟨rename (fun _ : Fin 1 => (0 : Fin 2)) p, ?_⟩
  have h : ((![X 0, 0] : Fin 2 → MvPolynomial (Fin 1) ℂ) ∘ fun _ : Fin 1 => (0 : Fin 2)) = X := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  simp only [lineMap, aeval_rename, h, aeval_X_left_apply]

def lineEquiv : (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.quotientKerAlgEquivOfSurjective lineMap_surjective

theorem lineIdeal_dim : ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) = (1 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv lineEquiv.toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

def lineProj : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := LinearMap.pi fun _ => LinearMap.proj 0

theorem lineEquiv_projAlgHom (p : MvPolynomial (Fin 1) ℂ) :
    lineEquiv (projAlgHom lineIdeal lineProj p) = p := by
  have h : (lineEquiv.toAlgHom.comp (projAlgHom lineIdeal lineProj)) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [Fin.fin_one_eq_zero i]
    simp [projAlgHom, lineEquiv, linPoly, lineProj, lineMap, Fin.sum_univ_two]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk lineMap_surjective (X 0)).trans
      (by simp [lineMap])
  exact congrArg (fun f => f p) h

theorem lineProj_finite : IsFiniteProjection lineIdeal lineProj := by
  have hinj : Function.Injective (projAlgHom lineIdeal lineProj) :=
    Function.LeftInverse.injective lineEquiv_projAlgHom
  have hsurj : Function.Surjective (projAlgHom lineIdeal lineProj) := by
    intro q
    refine ⟨lineEquiv q, lineEquiv.injective ?_⟩
    rw [lineEquiv_projAlgHom]
  exact ⟨hinj, RingHom.Finite.of_surjective _ hsurj⟩

def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval (0 : Fin n → ℂ))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
