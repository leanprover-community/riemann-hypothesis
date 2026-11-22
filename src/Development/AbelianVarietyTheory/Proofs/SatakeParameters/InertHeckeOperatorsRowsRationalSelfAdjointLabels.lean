module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorEqLabelOperatorLocalRepsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertRows

theorem ext_right_inv {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G)
    (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : G) (k : J) (hk : χ k = 1) :
    P.ext f (g * k) = P.ext f g := by
  have := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [hk, map_one, map_one, one_mul, Module.End.one_apply, Units.val_one, one_smul] at this

theorem ext_op_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : GQ V →* Module.End ℂ W) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K)
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ)
    {I : Type} (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End K S.Forms) (inR : I → Prop)
    (HT : Bridge.HeckeTie (Bridge.ratF V) Pr op inR (fun i => IsLabElt V (pl i) (ty i)) (fun i => IsLocElt V (pl i)))
    (i : I) (hi : inR i) (hgood : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl i ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i))
    (hpw : (ty i).Pairwise (fun a b => b ≤ a)) :
    IsLab V (pl i) (ty i) ∧ ∀ f : S.Forms, Pr.extL (op i f) = hkF V (pl i) (Finsupp.single (ty i) 1) (Pr.extL f) := by
  refine hβ.elim fun c hc => ?_
  have hc' : IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl i).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl i).isPrime.ne_top
  have hd := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc' (pl i) h1 hgood (ty i) (HT.hx i) (HT.hA i) hpw
    (HT.hx_ok i hi) (HT.hA_loc i hi) (HT.hDC i hi)
  exact ⟨hd.1, fun f => (HT.op_eq i hi f).trans (hd.2 W (Pr.ext f) fun g k hk =>
    ext_right_inv _ S σ ρ _ _ Pr f g k (HT.chi_loc i hi k hk))⟩

theorem csum_selfAdj {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G)
    (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms → M.H) (hj : ∀ x, M.e (j x) = P.extL x)
    (U : Module.End K S.Forms) (u : Module.End ℂ M.H) (hu : LinearMap.adjoint u = u) (hU : ∀ f, j (U f) = u (j f))
    (f g : S.Forms) :
    S.csum ((U f : S.Forms) : S.Cl → S.V) (g : S.Cl → S.V) = S.csum (f : S.Cl → S.V) ((U g : S.Forms) : S.Cl → S.V) := by
  have hs : ∀ f g : S.Forms, inner ℂ (j f) (j g) = σ (S.csum (f : S.Cl → S.V) (g : S.Cl → S.V)) := by
    intro f g
    rw [hM.2.2, hj, hj]
    exact (GlobalTheory.classPres_basic ι S σ ρ J χ P).2.1 f g
  apply σ.injective
  rw [← hs, ← hs, hU, hU, ← LinearMap.adjoint_inner_right, hu]

theorem dualC_single {d : List ℤ} (h : dualLab d = d) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single d 1 := by
  rw [Finsupp.mapRange_single, star_one, dualC, Finsupp.mapDomain_single, h]

end GlobalTheory.InertRows
