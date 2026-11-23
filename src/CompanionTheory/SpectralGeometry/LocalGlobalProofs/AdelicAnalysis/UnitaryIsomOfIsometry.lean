module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HIsom

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem conj_mem_UJ (s : A →+* A) (J : Matrix n n A) (G u : GL n A)
    (hu : u ∈ UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A))) :
    G * u * G⁻¹ ∈ UJ s J := by
  have hu' : cT s (u : Matrix n n A) * (cT s (G : Matrix n n A) * J * (G : Matrix n n A))
      * (u : Matrix n n A) = cT s (G : Matrix n n A) * J * (G : Matrix n n A) := hu
  have hGi : (G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A) = 1 := Units.mul_inv G
  change cT s (((G * u * G⁻¹ : GL n A)) : Matrix n n A) * J
    * (((G * u * G⁻¹ : GL n A)) : Matrix n n A) = J
  simp only [Units.val_mul]
  calc cT s ((G : Matrix n n A) * (u : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
        * ((G : Matrix n n A) * (u : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A))
      = cT s ((G⁻¹ : GL n A) : Matrix n n A)
          * (cT s (u : Matrix n n A) * (cT s (G : Matrix n n A) * J * (G : Matrix n n A))
            * (u : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A) := by
        simp only [cT_mul, Matrix.mul_assoc]
    _ = cT s ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
          * ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) := by
        rw [hu']; simp only [cT_mul, Matrix.mul_assoc]
    _ = J := by rw [hGi, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem conj_inv_mem_UJ (s : A →+* A) (J : Matrix n n A) (G u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) := by
  have hGi : (G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A) = 1 := Units.mul_inv G
  have key : cT s ((G⁻¹ : GL n A) : Matrix n n A)
      * (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A) = J := by
    calc cT s ((G⁻¹ : GL n A) : Matrix n n A)
          * (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A)
        = cT s ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
            * ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) := by
          simp only [cT_mul, Matrix.mul_assoc]
      _ = J := by rw [hGi, cT_one, Matrix.one_mul, Matrix.mul_one]
  have := conj_mem_UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) G⁻¹ u
    (by rw [key]; exact hu)
  simpa using this

def conjHomeo {T : Type} [Group T] [TopologicalSpace T] [ContinuousMul T] (H' H : Subgroup T) (G : T)
    (h₁ : ∀ u ∈ H', G * u * G⁻¹ ∈ H) (h₂ : ∀ u ∈ H, G⁻¹ * u * G ∈ H') : H' ≃ₜ* H where
  toFun u := ⟨G * u * G⁻¹, h₁ u u.2⟩
  invFun u := ⟨G⁻¹ * u * G, h₂ u u.2⟩
  left_inv u := by ext; simp [mul_assoc]
  right_inv u := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end Generic

section Base

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem cT_inclR (σ : E →ₐ[F] E) {M : ℕ} (g : Matrix (Fin M) (Fin M) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by
  ext i j
  simp [cT, sigR, inclR, Matrix.map_apply]

theorem JR_conj (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) :
    JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) =
      cT (sigR R σ) ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))
        * JR R J * ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  have hG : ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (g : Matrix (Fin M) (Fin M) E).map (inclR R) := rfl
  rw [hG, cT_inclR]
  simp only [JR, Matrix.map_mul]

end Base

theorem isTopologicalRing_tens (F E : Type) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing (R ⊗[F] E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

end GlobalTheory.CompanionTheory.SW.HIsom


open GlobalTheory.CompanionTheory.SW.HIsom in
theorem GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R], ∃ e : HA R σ J' ≃ₜ* HA R σ J, (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J' u * (bc (inclR R) g)⁻¹) ∧ ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J' u ∈ HFin R σ J' := by
  intro F E _ _ _ _ _ σ hCM M J _ g J' hJ' R _ _ _ _
  subst hJ'
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hJR := JR_conj R σ J g
  have h₁ : ∀ u ∈ HR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)),
      G * u * G⁻¹ ∈ HR R σ J := by
    intro u hu
    refine conj_mem_UJ (sigR R σ) (JR R J) G u ?_
    have : u ∈ UJ (sigR R σ) (JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E))) := hu
    rwa [hJR] at this
  have h₂ : ∀ u ∈ HR R σ J,
      G⁻¹ * u * G ∈ HR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) := by
    intro u hu
    change G⁻¹ * u * G ∈ UJ (sigR R σ) (JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)))
    rw [hJR]
    exact conj_inv_mem_UJ (sigR R σ) (JR R J) G u hu
  refine ⟨conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ _ u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem_UJ (σ : E →+* E) J g w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ _ u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem_UJ (σ : E →+* E) J g w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ _ u := hwu
    simp only [map_mul, map_inv, this, ← hG]
