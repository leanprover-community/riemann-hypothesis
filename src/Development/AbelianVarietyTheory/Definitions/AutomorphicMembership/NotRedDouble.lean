import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlagCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {F : Type} [Field F] {Z : Model Xo c β} {e : F ≃+* c.F}


theorem mono_genι (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Mono (genι Y) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)) :=
    IsLocalization.epi (nonZeroDivisors (𝓞 c.F)) c.F
  have : Mono (spMap (algebraMap (𝓞 c.F) c.F)) :=
    Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)).op
  infer_instance

theorem Lw_weightOf (C : FlagCpt Z e) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    C.Lw (GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)) = C.LEx (exKey Dw a n) := by
  have h : GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ) =
      GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ) + ((n / 2 : ℕ) : ℤ)) 0 := by
    funext τ j
    simp only [GlobalTheory.AllWt.weightOf]
    split_ifs <;> ring
  rw [FlagCpt.Lw, h, GlobalTheory.AllWt.exOf_weightOf]
  simp only [FlagCpt.LEx, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp [exKey, keyEx, ex, exZ]


theorem dim_count (f p q : ℕ) :
    f * ((p + q) * (p + q - 1) / 2) = f * p * q + f * (p * (p - 1) / 2) + f * (q * (q - 1) / 2) := by
  have h : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ' (p + q), Nat.choose_succ_succ' q, ih]
      simp only [Nat.choose_one_right]; ring
  simp only [← Nat.choose_two_right, h]; ring

theorem genericPt_eq (Y : GlobalTheory.ProjVar.Var F) (y : Y.X) :
    genericPt Y = spMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) ≫ stalkPt Y y :=
  (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y.X).specializes trivial)).symm

theorem cover {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}
    (Φ : FlagTor Z e U) (z : gen Z) : ∃ i, z ∈ Set.range (Φ.C i).π := by
  let k := AlgebraicClosure ((gen Z).residueField z)
  let x : Sp k ⟶ gen Z := spMap (algebraMap ((gen Z).residueField z) k) ≫ (gen Z).fromSpecResidueField z
  let φ : c.F →+* k := (Spec.preimage (x ≫ genStr Z)).hom
  have hφ : x ≫ genStr Z = spMap φ := (Spec.map_preimage _).symm
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z k φ x hφ
  obtain ⟨p, ⟨hp, -⟩, -⟩ := Φ.lifts k φ x hφ g
  let s : Sp k := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  refine ⟨p.1, p.2 s, ?_⟩
  rw [← Scheme.Hom.comp_apply, hp]
  exact Scheme.fromSpecResidueField_apply z _

theorem comp_eq {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) {k : Type} [Field k]
    [IsAlgClosed k] {φ : c.F →+* k} {x : Sp k ⟶ gen Z} (hx : x ≫ genStr Z = spMap φ) (g : EigFrame Z φ (x ≫ genι Z))
    {i j : U.Comp} {p : Sp k ⟶ (Φ.C i).Y.X} {q : Sp k ⟶ (Φ.C j).Y.X} (hp : p ≫ (Φ.C i).π = x) (hq : q ≫ (Φ.C j).π = x)
    (cp : (Φ.C i).Carries p g) (cq : (Φ.C j).Carries q g) : i = j :=
  congrArg Sigma.fst ((Φ.lifts k φ x hx g).unique (y₁ := ⟨i, p⟩) (y₂ := ⟨j, q⟩) ⟨hp, cp⟩ ⟨hq, cq⟩)



end GlobalTheory.ShFam.FlagCheck
