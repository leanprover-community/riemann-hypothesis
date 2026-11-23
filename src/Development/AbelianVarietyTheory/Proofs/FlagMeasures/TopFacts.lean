module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal

namespace GlobalTheory.ArchUnitaryTop

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n a : ℕ) (J : Matrix (Fin n) (Fin n) E), ContinuousSMul (HA (Ainf F) σ J) (Fin a → Fin n → Ainf F ⊗[F] E) ∧ BorelSpace (Fin a → Fin n → Ainf F ⊗[F] E) ∧ SecondCountableTopology (Fin a → Fin n → Ainf F ⊗[F] E) ∧ T2Space (Fin a → Fin n → Ainf F ⊗[F] E) ∧ IsTopologicalGroup (HA (Ainf F) σ J) ∧ LocallyCompactSpace (HA (Ainf F) σ J) ∧ SecondCountableTopology (HA (Ainf F) σ J) ∧ T2Space (HA (Ainf F) σ J) := by
  intro F E _ _ _ _ _ σ n a J
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e.secondCountableTopology
  haveI : T2Space (Ainf F ⊗[F] E) := e.isEmbedding.t2Space
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ n J
  refine ⟨⟨?_⟩, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsTopologicalGroup (HR (Ainf F) σ J)), h1, h2, h3⟩
  have hm : Continuous fun g : HA (Ainf F) σ J => HA.mat (Ainf F) σ J g :=
    continuous_subtype_val
  have hv : Continuous fun g : HA (Ainf F) σ J =>
      ((HA.mat (Ainf F) σ J g : GL (Fin n) (Ainf F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := Units.continuous_val.comp hm
  refine continuous_pi fun b => ?_
  exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.ArchUnitaryTop
