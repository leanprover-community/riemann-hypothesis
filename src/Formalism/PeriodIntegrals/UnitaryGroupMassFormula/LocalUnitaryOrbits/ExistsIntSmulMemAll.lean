module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section TopWs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem sdc_exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem exists_int_smul_mem_all (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) {ι : Type} [Fintype ι] (w : ι → Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ j, y • w j ∈ L := by
  classical
  choose y hy hw using fun j => sdc_exists_int_smul_mem L hL (w j)
  refine ⟨∏ j, y j, Finset.prod_ne_zero_iff.2 fun j _ => hy j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul]
  exact zsmul_mem (hw j) _

theorem ratV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem ratV_mem_latLoc {Λ : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ Λ) :
    ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem sdc_isOpen_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  apply PI.OmLocU.isOpen_latLoc <;> assumption

theorem sdc_isCompact_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  apply PI.OmLocU.isCompact_latLoc <;> assumption

theorem topW_holds (Λ : Set (Fin n → E)) (a : ℕ)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) : TopW v Λ a := by
  intro hL
  have e : LamT (E := E) v Λ a =
      Set.pi Set.univ (fun _ : Fin a => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT, Set.mem_pi]
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => sdc_isCompact_latLoc v Λ hL,
    isOpen_set_pi Set.finite_univ fun _ _ => sdc_isOpen_latLoc v Λ hFull⟩

end TopWs

end PI.OmLocU
