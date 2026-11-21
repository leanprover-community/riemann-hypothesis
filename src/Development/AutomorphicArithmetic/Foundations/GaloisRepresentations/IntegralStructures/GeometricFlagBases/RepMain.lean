import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagBasis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagMove
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGrHom
import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.EqZeroOfLowBlk
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.POpConj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.RelDim
import Development.EtaleCohomology.EtaleTrace.LFinCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtDesc
import Development.EtaleCohomology.WeilConjectures.AbsContPf
import Development.EtaleCohomology.WeilConjectures.ChevPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.VFinOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepAsm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem invariant_sup_alt {Γ k : Type} [Group Γ] [Field k] {d : ℕ} {ρ : Γ →* GL (Fin d) k}
    {U V : Submodule k (Fin d → k)} (hU : IsInv ρ U) (hV : IsInv ρ V) : IsInv ρ (U ⊔ V) := by
  intro g v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem_sup (hU g a ha) (hV g b hb)

private theorem invariant_inf {Γ k : Type} [Group Γ] [Field k] {d : ℕ} {ρ : Γ →* GL (Fin d) k}
    {U V : Submodule k (Fin d → k)} (hU : IsInv ρ U) (hV : IsInv ρ V) : IsInv ρ (U ⊓ V) := by
  intro g v hv
  exact ⟨hU g v hv.1, hV g v hv.2⟩

private theorem invariant_bot_alt {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊥ : Submodule k (Fin d → k)) := by
  intro g v hv
  rw [(Submodule.mem_bot k).1 hv, Matrix.mulVec_zero]
  exact Submodule.zero_mem _

theorem UpperTheory.Gal.Int.Geo.sSOfSum_of :
    SSOfSum := by
  intro Γ k _ _ d ρ B hB hS hT W hW
  obtain ⟨W', ⟨hinv, hdis⟩, hmax⟩ :=
    (wellFounded_gt (α := Submodule k (Fin d → k))).has_min
      {X | IsInv ρ X ∧ Disjoint W X} ⟨⊥, invariant_bot_alt ρ, disjoint_bot_right⟩
  have key : ∀ i, B i ≤ W ⊔ W' := by
    intro i
    rcases hS i (B i ⊓ (W ⊔ W')) (invariant_inf (hB i) (invariant_sup_alt hW hinv)) inf_le_left with h | h
    · have hd : Disjoint W (W' ⊔ B i) := by
        rw [Submodule.disjoint_def]
        intro w hw hw2
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw2
        have h2 : (a + b) + -a ∈ W ⊔ W' := Submodule.add_mem_sup hw (neg_mem ha)
        have h3 : (a + b) + -a = b := by abel
        rw [h3] at h2
        have hbU : b ∈ B i ⊓ (W ⊔ W') := ⟨hb, h2⟩
        rw [h] at hbU
        have hb0 : b = 0 := (Submodule.mem_bot k).1 hbU
        subst hb0
        rw [add_zero] at hw ⊢
        exact Submodule.disjoint_def.1 hdis a hw ha
      have hle : W' ⊔ B i ≤ W' := by
        by_contra hn
        exact hmax _ ⟨invariant_sup_alt hinv (hB i), hd⟩
          (lt_of_le_not_ge le_sup_left hn)
      exact (le_sup_right.trans hle).trans le_sup_right
    · exact inf_eq_left.1 h
  refine ⟨W', hinv, hdis, codisjoint_iff.2 ?_⟩
  exact top_le_iff.1 (hT ▸ iSup_le key)
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.contGL_of :
    ContGL := by
  intro Γ k _ _ _ _ _ _ d ρ
  constructor
  · intro hρ i j
    exact (Units.continuous_val.comp hρ).matrix_elem i j
  · intro h
    have hval : Continuous fun g : Γ => ((ρ g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) :=
      continuous_matrix h
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    have hinv : (fun g : Γ => (((ρ g)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)) =
        fun g => ((ρ g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) := by
      funext g
      rw [map_inv]
    rw [hinv]
    exact hval.comp continuous_inv
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.matEx_of :
    MatEx := by
  intro Γ L _ _ M _ _ a h1 hmul U hU d b
  let f : Γ → (U →ₗ[L] U) := fun g => (a g).restrict (fun x hx => hU g x hx)
  have hfv : ∀ g (x : U), ((f g x : U) : M) = a g (x : M) := fun g x => rfl
  have hf1 : f 1 = LinearMap.id := by
    ext x
    simp [hfv, h1]
  have hfm : ∀ g h, f (g * h) = f g ∘ₗ f h := by
    intro g h
    ext x
    simp [hfv, hmul]
  let φ : Γ →* Matrix (Fin d) (Fin d) L :=
    { toFun := fun g => LinearMap.toMatrix b b (f g)
      map_one' := by
        simp only [hf1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        simp only [hfm]
        exact LinearMap.toMatrix_comp b b b (f g) (f h) }
  let ρ : Γ →* GL (Fin d) L := φ.toHomUnits
  have hρ : ∀ g, ((ρ g : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = LinearMap.toMatrix b b (f g) :=
    fun g => MonoidHom.coe_toHomUnits φ g
  refine ⟨ρ, ?_, ?_⟩
  · intro g j
    simp only [hρ, LinearMap.toMatrix_apply]
    rw [← hfv]
    have e := congrArg Subtype.val (b.sum_repr (f g (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    exact e.symm
  · intro i j
    obtain ⟨μ, hμ⟩ := LinearMap.exists_extend (b.coord i)
    refine ⟨μ, fun g => ?_⟩
    rw [hρ, LinearMap.toMatrix_apply, ← hfv]
    have hc : μ (U.subtype (f g (b j))) = b.coord i (f g (b j)) := by
      rw [← LinearMap.comp_apply, hμ]
    rw [Module.Basis.coord_apply] at hc
    exact hc.symm
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem conj_basis {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (U : Submodule L M) {d : ℕ} (b : Module.Basis (Fin d) L U) (P : GL (Fin d) L) :
    ∃ b' : Module.Basis (Fin d) L U,
      ∀ j, (b' j).1 = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • (b i).1 := by
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) * (P : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let e : U ≃ₗ[L] U := LinearEquiv.ofLinear (Matrix.toLin b b (P : Matrix (Fin d) (Fin d) L))
    (Matrix.toLin b b ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L))
    (by rw [← Matrix.toLin_mul b b b, h1, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul b b b, h2, Matrix.toLin_one])
  refine ⟨b.map e, fun j => ?_⟩
  have h : e (b j) = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • b i :=
    Matrix.toLin_self b b _ j
  simp [h]

private theorem conj_mat {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (f : M →ₗ[L] M) {d : ℕ} (x y : Fin d → M) (A P Q : Matrix (Fin d) (Fin d) L) (hPQ : P * Q = 1)
    (hx : ∀ j, f (x j) = ∑ i, A i j • x i) (hy : ∀ j, y j = ∑ i, P i j • x i) (j : Fin d) :
    f (y j) = ∑ i, (Q * A * P) i j • y i := by
  have key : ∀ (B : Matrix (Fin d) (Fin d) L) (j : Fin d),
      ∑ i, B i j • y i = ∑ t, (P * B) t j • x t := by
    intro B j
    simp only [hy, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [key, show P * (Q * A * P) = A * P by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul], hy j]
  simp only [map_sum, map_smul, hx, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem UpperTheory.Gal.Int.Geo.matConj_of :
    MatConj := by
  intro l _ k _ H Ω _ _ L _ _ θ d ρ P ⟨b, hb⟩
  obtain ⟨b', hb'⟩ := conj_basis _ b P
  refine ⟨b', fun σ j => ?_⟩
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [cj_apply, Units.val_mul, Units.val_mul]
  exact conj_mat (galV l H Ω L σ) (fun i => (b i).1) (fun i => (b' i).1) _ _ _ h1 (hb σ) hb' j
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem l_unit (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) (Ω : Type) [Field Ω] [Algebra k Ω] :
    IsUnit (l : Γ(G3.sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (_root_.map_ne_zero _).mpr hl
  have h3 := h1.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa [map_natCast] using h3

theorem UpperTheory.Gal.Int.Geo.opUniq_of :
    G3.HopSpec → G3.OpEx.{1} → G3.OpEt → G3.EtGood → G3.BcSplits → OpUniq := by
  intro hHop hEx hEt hGood hBc l _ k _ hl H Ω _ _ g d hd T hT
  obtain ⟨hhop, -⟩ := hHop l hl H Ω g d hd
  have hsplit : G3.GalSplit (H.sΩ Ω g) := by
    unfold GlobalTheory.GalV.IsCorrOp at hT
    unfold G3.GalSplit
    obtain ⟨W, c, G, i1, i2, a, J, i3, σ, hG, hS, -⟩ := hT
    exact ⟨W, c, G, i1, i2, a, J, i3, σ, hG, hS⟩
  have hgood := hGood l (G3.sp Ω) (l_unit l hl Ω)
  haveI : IsFinite (H.s g) := hd.1
  haveI : Etale (H.s g) := hd.2.1
  have hbc := hBc (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) H.q (H.s g ≫ H.q) H.q (H.s g) rfl
    (𝟙 _) (Category.id_comp _) Empty (fun e => e.elim) (fun e => e.elim)
  haveI : IsFinite (H.sΩ Ω g) := hbc.1
  haveI : Etale (H.sΩ Ω g) := hbc.2.1
  let p : H.geomZ Ω ⟶ G3.sp Ω := pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
  have hcomm : H.tΩ Ω g ≫ p = H.sΩ Ω g ≫ p := by
    simp only [p, HTower.sΩ, HTower.tΩ, HTower.geomZ, geom, geomMap]
    erw [pullback.lift_snd, pullback.lift_snd]
  obtain ⟨A, -, huniq⟩ := (hEx (G3.et l (G3.sp Ω)) hgood p p (H.sΩ Ω g) (H.tΩ Ω g) hcomm).1 hsplit
  have h1 := huniq T ((hEt l p p _ _ hcomm T).mpr hT)
  have h2 := huniq (hop l H Ω g) ((hEt l p p _ _ hcomm _).mpr hhop)
  exact h1.trans h2.symm
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem comm_of_conj {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (A G G' : M →ₗ[R] M)
    (h : G ∘ₗ A ∘ₗ G' = A) (hid : G' ∘ₗ G = LinearMap.id) : A ∘ₗ G = G ∘ₗ A := by
  calc A ∘ₗ G = (G ∘ₗ A ∘ₗ G') ∘ₗ G := by rw [h]
    _ = G ∘ₗ A ∘ₗ (G' ∘ₗ G) := by simp only [LinearMap.comp_assoc]
    _ = G ∘ₗ A := by rw [hid, LinearMap.comp_id]

theorem UpperTheory.Gal.Int.Geo.hopGal_of :
    G3.HopSpec → OpConj → OpUniq → HopGal := by
  intro hS hC hU l _ k _ hl H Ω _ _ g d hd σ
  refine comm_of_conj _ _ (galTot l Ω H.q σ⁻¹)
    (hU l k hl H Ω g d hd _ (hC l k H Ω g _ σ (hS l hl H Ω g d hd).1)) ?_
  rw [← GlobalTheory.GalV.galTot_mul, inv_mul_cancel, GlobalTheory.GalV.galTot_one]
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.pieceStab_of :
    HopGal → PieceStab := by
  intro hG l _ k _ hl H hfet Ω _ _ L _ _ θ σ x hx
  simp only [piece, Submodule.mem_iInf] at hx ⊢
  intro g
  obtain ⟨d, hd⟩ := hfet g
  have hc := hG l k hl H Ω g d hd σ
  have hxg := hx g
  rw [Module.End.mem_eigenspace_iff] at hxg ⊢
  have e : (LinearMap.baseChange L (hop l H Ω g)) ((galV l H Ω L σ) x)
      = (galV l H Ω L σ) ((LinearMap.baseChange L (hop l H Ω g)) x) := by
    show ((LinearMap.baseChange L (hop l H Ω g)) ∘ₗ (LinearMap.baseChange L (galTot l Ω H.q σ))) x
      = ((LinearMap.baseChange L (galTot l Ω H.q σ)) ∘ₗ (LinearMap.baseChange L (hop l H Ω g))) x
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hc]
  rw [e, hxg, map_smul]
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.relDim_of :
    RelDim := by
  intro k _ X p hp hX
  haveI := hp
  haveI := hX
  haveI : ConnectedSpace X := inferInstance
  exact CrystallineSemistableComparison.exists_smoothOfRelativeDimension p
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.compSum_of :
    CompSum := by
  intro k _ X p hs hpr
  haveI := hs
  haveI := hpr
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : GlobalTheory.IsNormalScheme X := LateralTheory.EtaleTrace.LFinCut.normal_of_smooth p
  haveI : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ isCompact_univ⟩
  haveI : IsNoetherian X := {}
  haveI : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let e := Finite.equivFin (irreducibleComponents X)
  have hopen : ∀ Z : irreducibleComponents X, IsOpen (Z : Set X) :=
    fun Z => (GlobalTheory.IsNormalScheme.component Z).isOpen
  refine ⟨Nat.card (irreducibleComponents X), fun s => (GlobalTheory.IsNormalScheme.component (e.symm s) : Scheme),
    fun s => (GlobalTheory.IsNormalScheme.component (e.symm s)).ι, ⟨fun s => inferInstance, ?_, ?_⟩, ?_⟩
  · intro x
    refine ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    rw [Scheme.Opens.range_ι, Equiv.symm_apply_apply]
    exact mem_irreducibleComponent
  · intro s s' hss'
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have hne : e.symm s ≠ e.symm s' := fun h => hss' (e.symm.injective h)
    show Disjoint ((e.symm s : Set X)) ((e.symm s' : Set X))
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hn
    apply hne
    have h12 : ((e.symm s : Set X)) ⊆ (e.symm s' : Set X) :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen (e.symm s).2.1.isPreirreducible
        (hopen (e.symm s')) hn).trans
        (closure_minimal Set.inter_subset_right (isClosed_of_mem_irreducibleComponents _ (e.symm s').2))
    exact Subtype.ext (le_antisymm h12 ((e.symm s).2.2 (e.symm s').2.1 h12))
  · intro s
    haveI : IsReduced X := by
      haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
        obtain ⟨hd, -⟩ := ‹GlobalTheory.IsNormalScheme X›
        haveI := hd x
        infer_instance
      exact isReduced_of_isReduced_stalk X
    haveI : IrreducibleSpace ((GlobalTheory.IsNormalScheme.component (e.symm s) : X.Opens) : Set X) :=
      Subtype.irreducibleSpace (e.symm s).2.1
    exact isIntegral_of_irreducibleSpace_of_isReduced _
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.degFin_of :
    KunnethLefschetz.QDual → CrystallineSemistableComparison.InSum → A9 → KunnethLefschetz.ProjBC → KunnethLefschetz.SumCl → KunnethLefschetz.SumHl → KunnethLefschetz.PiBC → RelDim → CompSum → DegFin := by
  intro hQ hS a9 h1 h2 h5 h6 hR hC l _ k _ _ hk X p hp hproj
  have hprop : IsProper p := h1.2 _ p hproj
  obtain ⟨r, Y, j, hj, hY⟩ := hC k p hp hprop
  have hsm : ∀ s, Smooth (j s ≫ p) := fun s => by
    have := hj.1 s
    infer_instance
  choose d hd using fun s => hR k (j s ≫ p) (hsm s) (hY s)
  have hD : ∀ s, KunnethLefschetz.Dual l (d s) (Y s) := fun s => by
    have := hj.1 s
    have := h2 j hj s
    refine hQ l k hk (d s) (j s ≫ p) ⟨inferInstance, hd s⟩ ?_ (hY s)
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, j s ≫ i, inferInstance, by rw [Category.assoc]; exact congrArg (j s ≫ ·) e⟩
  have hb := fun n : ℤ => KunnethLefschetz.sumQ (l := l) h5 h6 hS j hj n
  refine ⟨fun n => ?_, ((2 * Finset.univ.sup d : ℕ) : ℤ), fun n hn => ?_⟩
  · have := fun s => (hD s).1 n
    exact FiniteDimensional.of_injective (LinearMap.pi fun s => LateralTheory.EtaleTrace.pb l (j s) n) (hb n).1
  · rcases hn with hn | hn
    · have hs : ∀ i, Subsingleton (HtL l i (sch.obj X) n 0) := fun i =>
        (a9 (ZMod (l ^ i)) (tw (l ^ i) 0)).1 _ n hn
      have : Subsingleton (Hl l (sch.obj X) n 0) :=
        ⟨fun a b => Subtype.ext (funext fun i => Subsingleton.elim _ _)⟩
      infer_instance
    · refine ⟨fun x y => (hb n).1 (funext fun s => ((hD s).2.1 n ?_).elim _ _)⟩
      have : d s ≤ Finset.univ.sup d := Finset.le_sup (Finset.mem_univ s)
      omega
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem finOfDeg {K : Type} [Field K] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module K (A n)] (hf : ∀ n, FiniteDimensional K (A n)) (N : ℤ)
    (hs : ∀ n, (n < 0 ∨ N < n) → Subsingleton (A n)) :
    FiniteDimensional K (DirectSum ℤ A) := by
  classical
  let S : Finset ℤ := Finset.Icc 0 N
  have hall : ∀ x : DirectSum ℤ A, x ∈ ⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i a =>
      by_cases hi : i ∈ S
      · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨a, rfl⟩)
      · have hout : i < 0 ∨ N < i := by
          simp only [S, Finset.mem_Icc, not_and_or, not_le] at hi
          exact hi
        haveI := hs i hout
        rw [Subsingleton.elim a 0, map_zero]
        exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have htop : (⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n)) = ⊤ :=
    eq_top_iff.2 (fun x _ => hall x)
  refine Module.finite_def.2 ?_
  rw [← htop]
  refine Submodule.fg_biSup S _ (fun n _ => ?_)
  rw [LinearMap.range_eq_map]
  exact (Module.finite_def.1 (hf n)).map _

theorem UpperTheory.Gal.Int.Geo.htotFin_of :
    DegFin → HtotFin := by
  intro h l _ k _ _ hl X p hp hproj
  obtain ⟨hf, N, hN⟩ := h l k hl p hp hproj
  exact finOfDeg hf N hN
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.stabOpen_of :
    HtDesc → StabOpen := by
  intro h l _ k Ω _ _ _ _ X p hqc hqs n i x m
  obtain ⟨L, hL, z, hz⟩ := h (l ^ m) k Ω p hqc hqs n i (x.1 m)
  have fix : ∀ τ ∈ L.fixingSubgroup,
      GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p τ)) (tw (l ^ m) i) n (x.1 m) = x.1 m := by
    intro τ hτ
    rw [← hz, ← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, LateralTheory.EWeil.StabPf.galMap_proj L p τ hτ]
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun g => g * σ⁻¹) ⁻¹' (L.fixingSubgroup : Set _), ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g * σ⁻¹ ∈ L.fixingSubgroup := hg
    have e : g = (g * σ⁻¹) * σ := by group
    show ((galHl l Ω p n i g) x).1 m = x.1 m
    rw [e, map_mul, Module.End.mul_apply]
    change GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p (g * σ⁻¹))) (tw (l ^ m) i) n
      (((galHl l Ω p n i σ) x).1 m) = x.1 m
    have hσ' : ((galHl l Ω p n i σ) x).1 m = x.1 m := hσ
    rw [hσ']
    exact fix _ hg'
  · exact (IntermediateField.fixingSubgroup_isOpen L).preimage (continuous_mul_right σ⁻¹)
  · show σ * σ⁻¹ ∈ L.fixingSubgroup
    rw [mul_inv_cancel]
    exact one_mem _
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.degCont_of :
    StabOpen → DegCont := by
  intro hst l _ k Ω _ _ _ _ X p hqc hqs n i hfin v μ
  have habs := LateralTheory.EWeil.AbsContPf.AbsCont_of LateralTheory.EWeil.ChevPf.Chev_of
  have key : ∀ (φ : Hl l (sch.obj (geom Ω p)) n i →ₗ[ℤ_[l]] ℚ_[l]) (x : Hl l (sch.obj (geom Ω p)) n i),
      Continuous fun σ : Gal(Ω/k) => φ (galHl l Ω p n i σ x) := by
    intro φ x
    refine habs l Gal(Ω/k) (Hl l (sch.obj (geom Ω p)) n i) (galHl l Ω p n i)
      (fun m => LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m))
      (LateralTheory.EWeil.ContinCut.evk_anti l _ n i) ?_ ?_ φ x
    · intro y hy
      apply Subtype.ext
      funext m
      simpa [LateralTheory.EWeil.ContinCut.evk] using hy m
    · intro y m
      have hset : {σ : Gal(Ω/k) | (galHl l Ω p n i σ) y - y ∈
          LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m)} =
          {σ | (galHl l Ω p n i σ y).1 m = y.1 m} := by
        ext σ
        simp [LateralTheory.EWeil.ContinCut.evk, sub_eq_zero]
      rw [hset]
      exact hst l k Ω p hqc hqs n i y m
  induction v using TensorProduct.induction_on with
  | zero => simpa using continuous_const
  | tmul q x =>
    have hφ := key ((μ.restrictScalars ℤ_[l]) ∘ₗ (TensorProduct.mk ℤ_[l] ℚ_[l] _ 1)) x
    refine (Continuous.mul (continuous_const : Continuous fun _ : Gal(Ω/k) => q) hφ).congr ?_
    intro σ
    have e : galHQ l Ω p n i σ (q ⊗ₜ x) = q • ((1 : ℚ_[l]) ⊗ₜ (galHl l Ω p n i σ x)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [GlobalTheory.EtC.galHQ]
    rw [e, map_smul, smul_eq_mul]
    rfl
  | add a b ha hb =>
    exact (ha.add hb).congr fun σ => by simp only [map_add, Pi.add_apply]
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.extCont_of :
    ExtCont := by
  intro Γ F L _ _ _ _ _ _ _ hF M _ _ _ a ha v μ
  induction v using TensorProduct.induction_on with
  | zero => simpa using continuous_const
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy
  | tmul l m =>
    let b := Module.finBasis F M
    have key : ∀ g, μ ((LinearMap.baseChange L (a g)) (l ⊗ₜ m)) =
        ∑ i, algebraMap F L (b.coord i (a g m)) * μ (l ⊗ₜ b i) := by
      intro g
      rw [LinearMap.baseChange_tmul]
      conv_lhs => rw [← b.sum_repr (a g m)]
      rw [TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L, map_smul, smul_eq_mul]
      rfl
    simp_rw [key]
    exact continuous_finset_sum _ fun i _ => (hF.comp (ha m (b.coord i))).mul continuous_const
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.totCont_of :
    GlobalTheory.GalV.VFin → DegCont → TotCont := by
  classical
  intro hVF hDC l _ k Ω _ _ _ _ hl X p hp v μ
  haveI := hp
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  have hu : IsUnit (l : Ω) := by
    have h := (map_ne_zero (algebraMap k Ω)).mpr hl
    rw [map_natCast] at h
    exact h.isUnit
  have hfin : ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l (sch.obj (geom Ω p)) n 0) := fun n =>
    (hVF l Ω hu (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) n 0).1
  have hv : ∀ σ, μ (galTot l Ω p σ v) = ∑ n ∈ v.support,
      (μ ∘ₗ DirectSum.lof ℚ_[l] ℤ (fun n => HQ l (sch.obj (geom Ω p)) n 0) n)
        (galHQ l Ω p n 0 σ (v n)) := by
    intro σ
    conv_lhs => rw [← DirectSum.sum_support_of v]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.comp_apply]
    congr 1
    exact DirectSum.lmap_lof (fun n => galHQ l Ω p n 0 σ) n (v n)
  simp_rw [hv]
  exact continuous_finset_sum _ fun n _ => hDC l k Ω p inferInstance inferInstance n 0 (hfin n) (v n) _
end

section
namespace UpperTheory.Gal.Int.Geo

theorem bcSplits : G3.BcSplits := G3.pBcSplits (G3.pSplitsBasic (G3.pSplitsPts G3.pIsoPts) G3.pPtsOfSplits)

theorem etGood : G3.EtGood := G3.pEtGood (G3.pEtnGood (G3.pFEtBasic G3.pPtsOfSplits) G3.pEtTr)

theorem galClos : G3.GalClos := G3.pGalClos (G3.pGalClosD (G3.pSplitsPts G3.pIsoPts) (G3.pOrdEx G3.pOrdStep))

theorem hopSpec : G3.HopSpec := G3.pHopSpec etGood (G3.pBcGood bcSplits (G3.pBcGal bcSplits)) galClos (G3.pOpEx G3.pOpTr)
  G3.pOpTr G3.pOpEt (G3.pOpBc bcSplits (G3.pBcGal bcSplits)) bcSplits

theorem grEx : GrEx := grEx_of flagEx_of flagBasis_of flagMove_of grHom_of (grSS_of grHom_of sSOfSum_of)

theorem hopGal : HopGal := hopGal_of hopSpec opConj_of (opUniq_of hopSpec (G3.pOpEx G3.pOpTr) G3.pOpEt etGood bcSplits)

theorem pieceStab : PieceStab := pieceStab_of hopGal

theorem degFin (h : KunnethLefschetz.Core) : DegFin :=
  degFin_of h.qDual KunnethLefschetz.inSum_holds h.inputs.a9 KunnethLefschetz.projBC_holds KunnethLefschetz.sumCl_holds KunnethLefschetz.sumHl_holds KunnethLefschetz.piBC_holds relDim_of compSum_of

theorem htotFin (h : KunnethLefschetz.Core) : HtotFin := htotFin_of (degFin h)

theorem degCont : DegCont := degCont_of (stabOpen_of htDesc_of)

theorem totCont (h : KunnethLefschetz.Core) : TotCont := totCont_of (vFin_of h.inputs) degCont

theorem repEx_core (h : KunnethLefschetz.Core) : RepEx :=
  repEx_of grEx contGL_of matEx_of matConj_of pieceStab (htotFin h) extCont_of (totCont h) KunnethLefschetz.projBC_holds

theorem repEx_holds : RepEx := repEx_core KunnethLefschetz.core_holds

end UpperTheory.Gal.Int.Geo
end
