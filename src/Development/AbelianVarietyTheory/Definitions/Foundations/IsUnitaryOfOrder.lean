module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne

@[expose] public section

noncomputable section
section

open NumberField IsDedekindDomain nonZeroDivisors

namespace GlobalTheory.Mem.Chr

variable (L : Type) [Field L] [NumberField L]

def hcharSub : Subgroup (Ideles L →* ℂˣ) where
  carrier := {χ | Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1}
  one_mem' := ⟨continuous_const, fun _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun k => by
    rw [MonoidHom.mul_apply, ha.2 k, hb.2 k, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨ha.1.inv, fun k => by rw [MonoidHom.inv_apply, ha.2 k, inv_one]⟩

abbrev HChar : Type := ↥(hcharSub L)

variable {L}

def atFin (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* (v.adicCompletion L)ˣ :=
  Units.map (algebraMap L (v.adicCompletion L)).toMonoidHom

def atInf (w : InfinitePlace L) : Lˣ →* (w.Completion)ˣ :=
  Units.map (algebraMap L w.Completion).toMonoidHom

def IsUnitAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = 1

def IsUnifAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = WithZero.exp (-1 : ℤ)

def ordF (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ℤ := -WithZero.log (v.valuation L (k : L))

def infDiag : Lˣ →* Ideles L := ∏ w : InfinitePlace L, (infIdele L w).comp (atInf w)

theorem exists_unif (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ, IsUnifAt v (atFin v k) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 π h0, ?_⟩
  show Valued.v ((π : L) : v.adicCompletion L) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]

def unif (v : HeightOneSpectrum (𝓞 L)) : Lˣ := Classical.choose (exists_unif v)

theorem unif_spec (v : HeightOneSpectrum (𝓞 L)) : IsUnifAt v (atFin v (unif v)) :=
  Classical.choose_spec (exists_unif v)

namespace HChar

variable (χ : HChar L)

def loc (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* ℂˣ := χ.1.comp (localIdele L v)

def locK (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* ℂˣ := (χ.loc v).comp (atFin v)

def inf : Lˣ →* ℂˣ := χ.1.comp infDiag

def UnrAt (v : HeightOneSpectrum (𝓞 L)) : Prop := ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ.loc v x = 1

def val (v : HeightOneSpectrum (𝓞 L)) : ℂˣ := χ.locK v (unif v)

def IsUnitary : Prop := ∀ x : Ideles L, ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1

def OrderDvd (n : ℕ) : Prop := χ ^ n = 1

def HasInf {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Prop :=
  ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i

def IsAbsPow (s : ℝ) : Prop :=
  (∀ v, χ.UnrAt v) ∧ (∀ v, ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))) ∧
    ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ)

def ProductRule : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 L)), (∀ v, v ∉ S → χ.UnrAt v) → ∀ k : Lˣ,
    χ.inf k * (∏ v ∈ S, χ.locK v k) * (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1

@[simp] theorem val_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ * χ').val v = χ.val v * χ'.val v := rfl
@[simp] theorem val_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ⁻¹).val v = (χ.val v)⁻¹ := rfl
@[simp] theorem inf_mul (χ χ' : HChar L) (k : Lˣ) : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
@[simp] theorem inf_inv (χ : HChar L) (k : Lˣ) : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl

end HChar

section Res

variable (F : Type) [Field F] [NumberField F] [Algebra F L]

variable {F}

variable (F)

end Res

end GlobalTheory.Mem.Chr

end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def OverP (p : ℕ) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal

instance psiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

variable {H}

end GlobalTheory.Mem.Chr

end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

namespace HChar

end HChar

end General

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem HChar.isUnitary_of_order {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) :
    χ.IsUnitary := fun x => by
  have h1 : (χ.1 x) ^ n = 1 := by
    have := congrArg (fun ξ : HChar L => ξ.1 x) h
    exact this
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2

end GlobalTheory.Mem.Chr

end
