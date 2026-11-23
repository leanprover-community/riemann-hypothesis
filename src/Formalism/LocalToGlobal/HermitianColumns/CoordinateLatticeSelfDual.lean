module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.Herm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def toGLb {V : Type} [AddCommGroup V] [Module E V] {n : ℕ} (b : Module.Basis (Fin n) E V) :
    (V ≃ₗ[E] V) ≃* GL (Fin n) E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

def AdStep {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (U : Subgroup (GL (Fin n) (E ⊗[F] Af F)))
    (y y' : GL (Fin n) (E ⊗[F] Af F)) (γ : GL (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ κ ∈ U, ∃ η ∈ UPts σ J (Af F), (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) η = 1) ∧
    bc (inclE (F := F) (Af F)) γ * y' = y * η * κ

def UAd (hc : CMData F E) (S : HSpace E) : Subgroup (GL (Fin S.rank) (E ⊗[F] AdeleRing (𝓞 F) F)) :=
  UPts hc.sig S.gram (AdeleRing (𝓞 F) F)

theorem mem_dual (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ ∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one,
    RingHom.mem_range]

theorem crdLat_dual (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    crdLat S (Formalism.HermitianLatticesTheory.dual S.hT L) = dualL hc S (crdLat S L) := by
  have key : ((crdLat S (Formalism.HermitianLatticesTheory.dual S.hT L) : Submodule (𝓞 E) (Fin S.rank → E)) : Set (Fin S.rank → E)) =
      dualSet (hc.sig : E →+* E) S.gram (crdLat S L) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩ s ⟨y, hy, rfl⟩
      have := (mem_dual S L x).1 hx y hy
      rw [hT_crd hc] at this
      exact this
    · intro ht
      refine ⟨(crd S).symm t, ?_, by simp⟩
      refine (mem_dual S L _).2 fun y hy => ?_
      rw [hT_crd hc]
      have := ht (crd S y) ⟨y, hy, rfl⟩
      simpa using this
  unfold dualL
  rw [← key, Submodule.span_eq]

theorem coordinate_lattice_self_dual (hc : CMData F E) (S : HSpace E) : dualL hc S (crdLat S S.L0) = crdLat S S.L0 := by
  rw [← crdLat_dual, show Formalism.HermitianLatticesTheory.dual S.hT S.L0 = S.L0 from S.baseLattice_isUnimodular]

end Formalism.L2.Herm

end
