module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem cp_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[l] →+* ℂ_[l]) = galCp τ :=
  RingHom.ext fun x => congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]) x

private theorem ainf_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (cp_eq σ τ h) _ _

private theorem away_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galAway σ = ACris.galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : AInf ℂ_[l] l)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, ACris.galAway_algebraMap, ACris.galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, ainf_eq σ τ h])

private theorem cris_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galCris σ = ACris.galCris τ := by
  have e : ACris.galZero σ = ACris.galZero τ := RingHom.ext fun y => Subtype.ext (by
    rw [ACris.coe_galZero, ACris.coe_galZero, away_eq σ τ h])
  rw [ACris.galCris, ACris.galCris, e]

theorem actEq : ActEq := by
  intro l _
  refine ⟨fun K g x => ?_, fun z => ?_⟩
  · exact RingHom.congr_fun (cris_eq _ _ fun _ => rfl) x
  · have h : (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)).comp ((Formalism.Per6.ainfMap l).comp (Formalism.Per6.zA l)) = zA l :=
      ringHom_ext_padicInt _ _
    exact congrArg (Formalism.Per6.cB l) (RingHom.congr_fun h z)

end UpperTheory.Gal.crystallineComparison.Br
