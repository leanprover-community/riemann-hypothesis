module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.AdicCompletionValuation

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance isModuleTopology_tens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

instance isTopologicalRing_tens : IsTopologicalRing (R ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem exists_homeomorph_tens :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (R ⊗[F] E ≃ₜ (ι → R)) := by
  let b := Module.finBasis F E
  let e : R ⊗[F] E ≃ₗ[R] (Fin (Module.finrank F E) → R) := (Algebra.TensorProduct.basis R b).equivFun
  exact ⟨Fin (Module.finrank F E), inferInstance, ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩⟩

variable [LocallyCompactSpace R] [T2Space R]

instance locallyCompactSpace_tens : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isClosedEmbedding.locallyCompactSpace

instance t2Space_tensorProduct_finiteExtension : T2Space (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isEmbedding.t2Space

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have e : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = (σ.toLinearMap.baseChange R : R ⊗[F] E → R ⊗[F] E) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [sigR, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

variable {M : ℕ}

instance locallyCompactSpace_mat : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
  inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))

instance t2Space_matrix_tensor : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
  inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))

theorem isClosed_HR (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
  have hc : Continuous fun g : GL (Fin M) (R ⊗[F] E) =>
      Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    unfold Formalism.UG.cT
    exact (((Units.continuous_val.matrix_map (continuous_sigR R σ)).matrix_transpose).matrix_mul
      continuous_const).matrix_mul Units.continuous_val
  exact isClosed_eq hc continuous_const

instance locallyCompactSpace_HR (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HR R σ J) :=
  (isClosed_HR R σ J).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance isTopologicalGroup_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) :=
  inferInstanceAs (IsTopologicalGroup (HR R σ J))

instance locallyCompactSpace_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HA R σ J) :=
  inferInstanceAs (LocallyCompactSpace (HR R σ J))

instance borelSpace_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

end Gen

end PI.AdicCompletionValuation
