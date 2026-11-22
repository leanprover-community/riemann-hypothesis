module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionTensor
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Unim

variable (Λ : Unim E)

instance : Module.Finite (𝓞 E) Λ.L := Module.Finite.iff_fg.2 Λ.isLattice.fg

instance : Module.Projective (𝓞 E) Λ.L :=
  have : Module.FinitePresentation (𝓞 E) Λ.L := Module.finitePresentation_of_finite _ _
  Module.Flat.projective_of_finitePresentation

section Group

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (a : OAct (𝓞 E) G)

end Group

omit [NumberField E] [IsCMField E] in
theorem mem_stdLat {n : ℕ} (x : Fin n → E) : x ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = x i := by
  simp [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Submodule.mem_one]

omit [NumberField E] [IsCMField E] in
theorem single_mem_stdLat {n : ℕ} (i : Fin n) : (Pi.single i 1 : Fin n → E) ∈ Formalism.L2.Pj.stdLat E n :=
  (mem_stdLat _).2 fun j => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
    by_cases h : j = i <;> simp [h]⟩

variable (E) in
def stdEquiv (n : ℕ) : Formalism.L2.Pj.stdLat E n ≃ₗ[𝓞 E] (Fin n → 𝓞 E) where
  toFun x i := ⟨x.1 i, by obtain ⟨c, hc⟩ := (mem_stdLat _).1 x.2 i; exact hc ▸ c.isIntegral_coe⟩
  invFun v := ⟨fun i => algebraMap (𝓞 E) E (v i), (mem_stdLat _).2 fun i => ⟨v i, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [NumberField E] [IsCMField E] in
theorem isLattice_stdLat (n : ℕ) : Submodule.IsFullLattice E (Formalism.L2.Pj.stdLat E n) := by
  have hspan : Submodule.span E (Formalism.L2.Pj.stdLat E n : Set (Fin n → E)) = ⊤ :=
    eq_top_iff.2 fun x _ => by
      rw [pi_eq_sum_univ' x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLat i))
  refine { toIsLattice := ?_, span_eq_top := hspan }
  refine (Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank E _).2 ⟨?_, ?_⟩
  · exact Module.Finite.iff_fg.1 (Module.Finite.equiv (stdEquiv E n).symm)
  · rw [hspan, finrank_top, (stdEquiv E n).finrank_eq, Module.finrank_fin_fun, Module.finrank_fin_fun]

end Unim

variable {H : Host E} {X X' : Scheme.{0}}

theorem bar_eq_star (H : Host E) (c : 𝓞 E) : H.bar c = star c := RingOfIntegers.ext (H.bar_eq c)

namespace tens

variable (t : SAB H X) (Λ : Unim E)

variable {t} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)

end tens

section Record

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

end Record

end GlobalTheory.LocM
