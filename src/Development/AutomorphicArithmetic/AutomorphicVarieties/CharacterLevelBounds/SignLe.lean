module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigSign
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem aux {O W M : Type} [CommRing O] [IsDomain O] [Group W] [AddCommGroup M] [Module O M] {N : ℕ} [NeZero N]
    (H : Subgroup (ZMod N)ˣ) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))]
    (π : Representation O W M) (cl : W →* (ZMod N)ˣ) (hcl : Function.Surjective cl)
    (hker : ∀ g, cl g ∈ H → ∀ x, π g x = x) (h2 : IsUnit (2 : O)) (s : ℕ) (c : W) (hcc : cl c = -1)
    (T : Finset (DirichletCharacter O N)) (hT : evenSet O H s ⊆ ↑T) :
    Module.length O (Module.End.eigenspace (π c) ((-1 : O) ^ s)) ≤
      ∑ χ ∈ T, Module.length O (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        ((χ.toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype)) := by
  classical
  let _ : Fintype (((ZMod N)ˣ ⧸ H) →* Oˣ) := Fintype.ofFinite _
  let p : W →* (ZMod N)ˣ ⧸ H := (QuotientGroup.mk' H).comp cl
  have hp : Function.Surjective p := (QuotientGroup.mk'_surjective H).comp hcl
  have hpc : p c = QuotientGroup.mk' H (-1) := by
    show QuotientGroup.mk' H (cl c) = _
    rw [hcc]
  let f : (((ZMod N)ˣ ⧸ H) →* Oˣ) → DirichletCharacter O N := fun ψ =>
    MulChar.ofUnitHom (ψ.comp (QuotientGroup.mk' H))
  have hf : ∀ ψ, (f ψ).toUnitHom = ψ.comp (QuotientGroup.mk' H) := fun ψ =>
    MulChar.equivToUnitHom.apply_symm_apply _
  have finj : Function.Injective f := fun ψ ψ' h => by
    have h' : ψ.comp (QuotientGroup.mk' H) = ψ'.comp (QuotientGroup.mk' H) := by rw [← hf, ← hf, h]
    exact (MonoidHom.cancel_right (QuotientGroup.mk'_surjective H)).1 h'
  have key := lenEigSign O W ((ZMod N)ˣ ⧸ H) M π p hp
    (fun g hg x => hker g ((QuotientGroup.eq_one_iff _).1 hg) x) h2 c ((-1) ^ s)
    (by rw [hpc, ← map_mul]; simp) (by rw [← mul_pow]; simp)
    (Finset.univ.filter fun ψ => ψ (p c) = (-1) ^ s) (fun ψ h => by simpa using h)
  have hs : (((-1 : Oˣ) ^ s : Oˣ) : O) = (-1) ^ s := by simp
  rw [hs] at key
  refine key.trans ?_
  have hE : ∀ ψ : ((ZMod N)ˣ ⧸ H) →* Oˣ, eig π (ψ.comp p) =
      eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        (((f ψ).toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype) := by
    intro ψ
    ext x
    rw [mem_eig, mem_eig, hf]
    exact ⟨fun h g => h g.1, fun h g => h ⟨g, trivial⟩⟩
  rw [Finset.sum_congr rfl fun ψ _ => congrArg (fun S : Submodule O M => Module.length O S) (hE ψ),
    ← Finset.sum_image (f := fun χ : DirichletCharacter O N => Module.length O
      (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        ((χ.toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype))) finj.injOn]
  refine Finset.sum_le_sum_of_subset fun χ hχ => ?_
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hχ
  have hψ' := (Finset.mem_filter.1 hψ).2
  refine hT ⟨fun u hu => ?_, ?_⟩
  · rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu, map_one]
  · have : f ψ (((-1 : (ZMod N)ˣ)) : ZMod N) = (((f ψ).toUnitHom (-1) : Oˣ) : O) := (MulChar.coe_toUnitHom _ _).symm
    rw [hf, MonoidHom.comp_apply, ← hpc, hψ', hs] at this
    simpa using this

theorem UpperTheory.V.Chr.signLe :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))], l ≠ 2 → ∀ (e s : ℕ) (c : G ℚ Ω), IsConjOm c.toRingEquiv →
          ∀ T : Finset (DirichletCharacter O N), evenSet O H s ⊆ ↑T →
          Module.length O (Module.End.eigenspace (shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H) c) ((-1 : O) ^ s)) ≤
            ∑ χ ∈ T, eigL l e (levH ℚ Ω H) (dirG ℚ Ω χ) := by
  intro Ω _ _ _ N _ H l hl O _ _ _ _ _ _ hl2 e s c hc T hT
  have h2 : IsUnit (2 : O) := by
    have := (dvrFacts l O).2.2.2.2.2.2.2.2 2 fun h =>
      hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    simpa using this
  have hker : ∀ g, cls ℚ Ω N g ∈ H → ∀ x, shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H) g x = x :=
    fun g hg x => selRep_of_mem _ (levH ℚ Ω H) _ (g := g) (Subgroup.mem_comap.2 hg) x
  exact aux H (shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H)) (cls ℚ Ω N) (clsOnto Ω N).1
    hker h2 s c ((clsFacts ℚ Ω N).2.2.2.1 c hc) T hT
