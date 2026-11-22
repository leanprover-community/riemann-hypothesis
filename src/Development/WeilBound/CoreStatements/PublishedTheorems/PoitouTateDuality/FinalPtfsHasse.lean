module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalGenDefs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmpA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Hasse

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem urChar_mul (N : ℕ+) (g h : Gal(Ω/K)) :
    urChar K Ω N (g * h) = urChar K Ω N g + urChar K Ω N h := by
  simp only [urChar, map_mul, toAdd_mul, map_add (f := _)]

theorem urChar_one (N : ℕ+) : urChar K Ω N 1 = 0 := by
  simp only [urChar, map_one, toAdd_one, map_zero]

theorem urChar_of_ker (N : ℕ+) {g : Gal(Ω/K)} (hg : unramifiedDegree K Ω g = 1) :
    urChar K Ω N g = 0 := by
  simp only [urChar, hg, toAdd_one, map_zero]

theorem urChar_of_deg_one (N : ℕ+) {g : Gal(Ω/K)}
    (hg : unramifiedDegree K Ω g = Multiplicative.ofAdd 1) : urChar K Ω N g = 1 := by
  simp only [urChar, hg, toAdd_ofAdd, map_one]

theorem continuous_urChar (N : ℕ+) : Continuous (urChar K Ω N) :=
  continuous_unramifiedCoord (K := K) (Ω := Ω) N

def urPsi (N : ℕ+) : Additive Gal(Ω/K) →ₜ+ QZ where
  toFun a := zmodToQZ (N : ℕ) (urChar K Ω N (Additive.toMul a))
  map_zero' := by simp only [toMul_zero, urChar_one, map_zero]
  map_add' a b := by simp only [toMul_add, urChar_mul, map_add (f := _)]
  continuous_toFun :=
    (continuous_of_discreteTopology.comp (continuous_urChar (K := K) (Ω := Ω) N)).comp
      continuous_toMul

theorem reprIco_urPsi (N : ℕ+) (g : Gal(Ω/K)) :
    reprIco (charAdd (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g)) =
      ((urChar K Ω N g).val : ℚ) / (N : ℕ) := by
  rw [charAdd_apply]
  have h1 : (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g) =
      QZ.mk (((urChar K Ω N g).val : ℤ) / ((N : ℕ) : ℤ)) := by
    show zmodToQZ (N : ℕ) (urChar K Ω N g) = _
    conv_lhs => rw [← ZMod.intCast_zmod_cast (urChar K Ω N g)]
    rw [zmodToQZ_intCast, ZMod.cast_eq_val]
    push_cast
    rfl
  rw [h1]
  have h2 : QZ.toAddCircle (QZ.mk (((urChar K Ω N g).val : ℤ) / ((N : ℕ) : ℤ))) =
      ((((urChar K Ω N g).val : ℚ) / (N : ℕ) : ℚ) : AddCircle (1 : ℚ)) := by
    simp [QZ.mk]
  rw [h2, reprIco_coe]
  have hN : (0 : ℚ) < (N : ℕ) := by exact_mod_cast N.pos
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hN]
  exact_mod_cast ZMod.val_lt (urChar K Ω N g)

theorem charCocycle_urPsi (N : ℕ+) (g h : Gal(Ω/K)) :
    ((N : ℕ) : ℤ) * charCocycle (charAdd (urPsi (K := K) (Ω := Ω) N)) (g, h) =
      ((urChar K Ω N g).val : ℤ) + (urChar K Ω N h).val - (urChar K Ω N (g * h)).val := by
  have e := charCocycle_cast (charAdd (urPsi (K := K) (Ω := Ω) N)) g h
  rw [reprIco_urPsi, reprIco_urPsi, reprIco_urPsi] at e
  have hN : ((N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast N.ne_zero
  have : (((N : ℕ) : ℤ) * charCocycle (charAdd (urPsi (K := K) (Ω := Ω) N)) (g, h) : ℚ) =
      (((urChar K Ω N g).val : ℤ) + (urChar K Ω N h).val - (urChar K Ω N (g * h)).val : ℤ) := by
    push_cast
    rw [e]
    field_simp
  exact_mod_cast this

end Hasse

section HasseC

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

end HasseC

section HasseMain

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

end HasseMain

end PositivityTheory.Lit1.PTN
