module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SqChartCore
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain MeasureTheory Topology
open HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.SiegelWeilConvCompare

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  apply _root_.PI.AprimeInfW.sq_coord_tens <;> assumption

section Zero

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [Subsingleton V]

end Zero

theorem measure_fundamentalDomain_pos (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ) (hμ : IsHaarH F E σ M J μ)
    (𝓕) (h : IsFDH F E σ M J μ 𝓕) : 0 < μ 𝓕 := by
  haveI : μ.IsHaarMeasure := hμ
  haveI : Countable E := (Module.Free.chooseBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  haveI : Countable (HFin (AF F) σ J) := by
    have : ((HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
        Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      unfold HFin; rw [Subgroup.coe_map]; exact (Set.to_countable _).image _
    exact this
  haveI : Countable (HFinIn (AF F) σ J) := by
    have : Function.Injective (fun x : HFinIn (AF F) σ J => (⟨x.1.1, x.2⟩ : HFin (AF F) σ J)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : HFin (AF F) σ J => z.1) hxy))
    exact this.countable
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
    ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
  exact pos_iff_ne_zero.2 (IsFundamentalDomain.measure_ne_zero (NeZero.ne μ) h)

section HermTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def tensHomeo {κ : Type} [Finite κ] (b : Module.Basis κ F E) : R ⊗[F] E ≃ₜ (κ → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

end HermTop

end GlobalTheory.SiegelWeilConvCompare
