module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.InflAct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.InflUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaModel
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base


theorem UpperTheory.V.Base.shaLenEq :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      shaLen D e = Module.length ℤ_[l] (ShaU (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω)) ∧
      ∀ [Normal k E] (τ : E ≃+* E) (σ : G k Ω), IsLift τ σ.toRingEquiv → ∀ s : ℤ_[l],
        Module.length ℤ_[l] ↥(Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s) =
          Module.length ℤ_[l] (Module.End.eigenspace (shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ) s) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨Φ, hΦ⟩ := shaModel k E Ω l D e
  refine ⟨Φ.length_eq, ?_⟩
  intro _ τ σ hτσ s
  have key : ∀ x : ↥(Sha D e), ∃ h : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e,
      Φ ⟨_, h⟩ = shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ (Φ x) := by
    intro x
    set y := shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ (Φ x) with hy
    have h1 : Infl k D e (galoisActionOnCohomology D e τ (x : H1 (qzTw D e))) (y : H1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω)) :=
      inflAct k E Ω l D e τ σ hτσ _ _ (hΦ x)
    have h2 := hΦ (Φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at h2
    have heq : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) = ((Φ.symm y : ↥(Sha D e)) : H1 (qzTw D e)) :=
      ((inflUnique k E Ω l D e).2 _ _ _ _ h1 h2).2 rfl
    have hmem : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e := by
      rw [heq]
      exact (Φ.symm y).2
    refine ⟨hmem, ?_⟩
    have hsub : (⟨_, hmem⟩ : ↥(Sha D e)) = Φ.symm y := Subtype.ext heq
    rw [hsub, LinearEquiv.apply_symm_apply]
  have hle : Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s ≤ Sha D e := inf_le_left
  have hmap : Submodule.map (Φ : ↥(Sha D e) →ₗ[ℤ_[l]] ↥(ShaU (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω)))
      (Submodule.comap (Sha D e).subtype (Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s)) =
      Module.End.eigenspace (shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ) s := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext y
    obtain ⟨h, hk⟩ := key (Φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at hk
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    refine ⟨fun hx => ?_, fun hx => ⟨(Φ.symm y).2, ?_⟩⟩
    · have hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y := Subtype.ext hx.2
      refine hk.symm.trans ?_
      rw [hs, Φ.map_smul, LinearEquiv.apply_symm_apply]
    · have hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y := by
        apply Φ.injective
        refine hk.trans (hx.trans ?_)
        rw [Φ.map_smul, LinearEquiv.apply_symm_apply]
      exact congrArg Subtype.val hs
  rw [← hmap]
  exact ((Submodule.comapSubtypeEquivOfLe hle).symm.trans (Φ.submoduleMap _)).length_eq
