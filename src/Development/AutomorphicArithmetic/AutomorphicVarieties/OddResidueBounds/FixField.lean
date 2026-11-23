module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem cyc_hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] [CharZero Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have e : f.toRatAlgHom = g.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact h _ hζ.pow_eq_one
  exact RingHom.ext fun x => DFunLike.congr_fun e x

theorem UpperTheory.V.Odd.fixField :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∃ (K : IntermediateField E Ω) (_ : NumberField K) (_ : IsCyclotomicExtension {N} ℚ K), galOf E K Ω = fixMu E Ω N ∧ ∀ (b : (ZMod N)ˣ) (σ : Ω ≃+* Ω), CycLift N b σ → IsLift (Stick.sg N K b).toRingEquiv σ := by
  intro E Ω _ _ _ _ _ N _ ρ hρ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq fun q => by simp
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : IsGalois ℚ Ω := {}
  haveI : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {ζ}
  have hζL : ζ ∈ L := IntermediateField.mem_adjoin_simple_self ℚ ζ
  have hE : ∀ e : E, algebraMap E Ω e ∈ L := fun e => by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 : σ ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ ζ hζL
    have hc : CycLift N 1 σ.toRingEquiv := fun x hx => by
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
      have h2 : σ x = x := by rw [← hi, map_pow, h1]
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]
      exact h2
    have := hρ 1 _ hc e
    rw [map_one] at this
    exact this
  let K : IntermediateField E Ω := L.toSubfield.toIntermediateField hE
  haveI hL : IsCyclotomicExtension {N} ℚ L := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  let φ : L ≃+* K := RingEquiv.refl L
  have hK : @IsCyclotomicExtension {N} ℚ K _ _ DivisionRing.toRatAlgebra :=
    @IsCyclotomicExtension.equiv {N} ℚ L _ _ _ K _ DivisionRing.toRatAlgebra hL
      (@AlgEquiv.ofRingEquiv ℚ L K _ _ _ _ DivisionRing.toRatAlgebra φ fun q => by simp)
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : NumberField K := IsCyclotomicExtension.numberField {N} ℚ K
  have hmu : ∀ x : Ω, x ^ N = 1 → x ∈ K := fun x hx => by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact (pow_mem hζL i : ζ ^ i ∈ L)
  have hpow : ∀ x : K, x ^ N = 1 → algebraMap K Ω x ^ N = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  refine ⟨K, inferInstance, hK, ?_, fun b σ hσ x => ?_⟩
  · ext g
    refine ⟨fun h x hx => h ⟨x, hmu x hx⟩, fun h x => ?_⟩
    exact DFunLike.congr_fun (cyc_hom_ext N (g.toRingEquiv.toRingHom.comp (algebraMap K Ω)) (algebraMap K Ω)
      fun y hy => h _ (hpow y hy)) x
  · refine DFunLike.congr_fun (cyc_hom_ext N (σ.toRingHom.comp (algebraMap K Ω))
      ((algebraMap K Ω).comp (Stick.sg N K b).toRingEquiv.toRingHom) fun y hy => ?_) x
    change σ (algebraMap K Ω y) = algebraMap K Ω (Stick.sg N K b y)
    rw [hσ _ (hpow y hy), Stick.sg_apply N K b hy, map_pow]
