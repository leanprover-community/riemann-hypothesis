module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.locCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCount D' ε' d → LocCount D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε h R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hdual
  let σ : D' →* D := α.symm.toMulEquiv.toMonoidHom
  have hσ : ∀ g, σ g = α.symm g := fun g => rfl
  let ρ2 : Representation R D' M := ρ.comp σ
  let ρ2' : Representation R D' M' := ρ'.comp σ
  have heps : ∀ g : D', epsBar ε (α.symm g) = epsBar ε' g := by
    intro g
    simp only [epsBar, hε, ContinuousMulEquiv.apply_symm_apply]
  have hLC2 : LC ρ2 := fun m => (hLC m).comp_continuous α.symm.continuous
  have hdual2 : IsDualPair ε' ρ2 ρ2' b := by
    refine ⟨hdual.left, hdual.right, fun g x y => ?_⟩
    have := hdual.equiv (α.symm g) x y
    rw [← heps g, ← this]
    rfl
  obtain ⟨hfin, hcard⟩ := h R M M' ρ2 ρ2' b hLC2 hdual2
  let e : Zl ρ ≃ Zl ρ2 :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.symm.continuous, fun g k => ?_⟩
        show z.1 (α.symm (g * k)) = z.1 (α.symm g) + ρ (α.symm g) (z.1 (α.symm k))
        rw [map_mul]
        exact hz2 _ _⟩
      invFun := fun z => ⟨fun g => z.1 (α g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.continuous, fun g k => ?_⟩
        have := hz2 (α g) (α k)
        rw [← map_mul] at this
        show z.1 (α (g * k)) = z.1 (α g) + ρ g (z.1 (α k))
        rw [this]
        show z.1 (α g) + ρ (α.symm (α g)) (z.1 (α k)) = _
        rw [ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α.symm (α g)) = z.1 g
        rw [ContinuousMulEquiv.symm_apply_apply]
      right_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α (α.symm g)) = z.1 g
        rw [ContinuousMulEquiv.apply_symm_apply] }
  have hinv : Nat.card ρ2'.invariants = Nat.card ρ'.invariants := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    simp only [Representation.mem_invariants]
    constructor
    · intro hv g
      have := hv (α g)
      simpa [ρ2', hσ] using this
    · intro hv g
      exact hv (α.symm g)
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hcard, hinv]
