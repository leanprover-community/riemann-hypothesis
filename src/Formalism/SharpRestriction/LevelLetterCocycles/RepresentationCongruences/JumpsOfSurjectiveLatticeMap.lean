module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem jumps_of_surjective_lattice_map : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hJ : UsedJ D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL),
    (∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L),
      Formalism.MainNotions.LiftingTheory.Sur ((HW l).W K 1 LL hG) f →
      ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV ((D.loc l).PD K) T₂.ρ τ a →
        IsJumpV ((D.loc l).PD K) T₁.ρ τ a) ∧
    (∀ (T₂ Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₂.L Y.L)
      (π : LatHom Y.L ((HW l).W K 1 LL hG).one.L) (cc : ↥(GK K) → T₂.V),
      cc ∈ latticeCocycles T₂.L → IsCrys ((D.loc l).PD K) T₂.ρ → IsCrys ((D.loc l).PD K) Y.ρ →
      Formalism.MainNotions.LiftingTheory.IsExtOf ((HW l).W K 1 LL hG) ι π cc →
      ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV ((D.loc l).PD K) Y.ρ τ a →
        a = 0 ∨ IsJumpV ((D.loc l).PD K) T₂.ρ τ a) := by
  intro D HW F hJ l _ K LL hG
  refine ⟨?_, ?_⟩
  · intro T₁ T₂ f hS τ a ha
    obtain ⟨c1, c2, hO⟩ := hS
    obtain ⟨T₀, ι, hses, c0⟩ := Formalism.MainNotions.LiftingTheory.lker_HKer_D D HW F hJ.a22 l K 1 LL hG T₁ T₂ f ⟨c1, c2, hO⟩
    exact (hJ.a23 l K LL T₀ T₁ T₂ ι f hses c0 c1 c2 τ a).2 (Or.inr ha)
  · intro T₂ Y ι π cc _ c2 cY hext τ a ha
    obtain ⟨cone, hone0⟩ := Formalism.MainNotions.LiftingTheory.lone_HOne0_holds D HW F l K 1 LL hG
    rcases (hJ.a23 l K LL T₂ Y _ ι π hext.1 c2 cY cone τ a).1 ha with h | h
    · exact Or.inr h
    · exact Or.inl (hone0 τ a h)

end Formalism.MainNotions.N.Ln17
