import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AuxUOfFirstTheoremPlaceBound

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def ea_geR {K : Type} [Field K] (p : ℕ) (R : Subring K) (x : K) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : K) ^ (-a) ∈ R


variable {p : ℕ} [Fact p.Prime] {X : Sys p}

abbrev ea_K (Y : Pend X) : Type := AlgebraicClosure Y.Kc



theorem ea_applyD_map {σ τ K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : φ.comp (Int.castRingHom K) = Int.castRingHom K' := RingHom.ext_int _ _
  have e2 : φ (∏ x ∈ n.support, ((n x).factorial : K)) = ∏ x ∈ n.support, ((n x).factorial : K') := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun x _ => map_natCast φ _
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, e, MvPowerSeries.coeff_map, map_mul φ, e2]

def ea_InClassA (X : Sys p) {K' : Type} [Field K'] (R' : Subring K') (j : ℕ) (h F : MvPowerSeries (X.ZA j) K') : Prop :=
  ∃ g : ℕ → MvPowerSeries (X.ZA j) K', (∀ i, IntR R' (g i)) ∧ ∀ α : X.ZA j →₀ ℕ,
    MvPowerSeries.coeff α F = ∑ i ∈ range (α.degree + 1),
      (((p : K') ^ i)⁻¹ * MvPowerSeries.coeff α (h ^ i * g i))

def ea_RestSU (X : Sys p) (Y : Pend X) : Prop :=
  DworkLemma p → BeProp p Y.be → ∀ (v : X.Pl) (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc),
    IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra Y.Kc K'] [IsScalarTower (K0 p) Y.Kc K'] (R' : Subring K')
      (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ Y.Oc, algebraMap Y.Kc K' x ∈ R') →
      ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧
        ea_InClassA X R' j (X.hhA K' j v u) (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))))

structure ea_Cls (X : Sys p) (j : ℕ) (v : X.Pl) (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K') : Prop where
  vp_pow : vp ^ (p ^ 2 - 1) = (p : K')
  Rp_le : Rp p K' vp ≤ R'
  val : ∀ x : K', x ∈ R' ∨ x⁻¹ ∈ R'
  cls : ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧ ea_InClassA X R' j (X.hhA K' j v u) (atPi vp F)

def SeriesGaussValuationFirst (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (X.PIv j I v) F)) (X.g0v v (j + 1))

def SeriesGaussValuationSecond (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (X.PIv j I v) F)) (X.gv v (j + 1) - X.alEven v)

def ea_RestKerB (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K')
    (vp : K') (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (PIvS X j I (fun _ => i) v) F)) (X.gv v (j + 1))





end Formalism.MainNotions.FormalGroupSystem.Pf
