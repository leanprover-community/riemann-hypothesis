import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.PevExp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SqExpH
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TorFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangularStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExistsDual
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.RFinEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNearH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOffHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EmbProjHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.NeatOfPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightAtEmbeddingOverPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SepPoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NearSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.Pieces
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamSum

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.evLem_of :
    UpperTheory.Gal.Wt.EvLem := by
  intro M X Z _ _ _ ev hsep T Φ hT L
  let W : Submodule ℂ (Module.Dual ℂ M) := Submodule.span ℂ (Set.range ev)
  have hbot : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Submodule.mem_dualCoannihilator] at hm
    exact (Submodule.mem_bot ℂ).2 (hsep m fun x => hm _ (Submodule.subset_span ⟨x, rfl⟩))
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hbot, Submodule.dualAnnihilator_bot]
  let φ : Module.Dual ℂ M →ₗ[ℂ] (Z → ℂ) :=
    { toFun := fun l z => l (Φ z)
      map_add' := fun a b => by
        ext z
        simp
      map_smul' := fun c a => by
        ext z
        simp }
  have hle : W ≤ T.comap φ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hT x
  have hL : L ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  exact hle hL
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.dom_of :
    UpperTheory.Gal.Wt.Dom := by
  classical
  intro a κ f hf
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ a a κ.natW := hf
  clear hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ a a κ.natW] at hf'
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm k
    have h := (Formalism.GradedWeylDivisibility.bidetDominance ℂ a a K sz hsz I m hm).1 k
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm k
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx m h k
    · exact hy m h k
  | smul c x _ hx =>
    intro m hm k
    exact hx m (MvPolynomial.support_smul hm) k
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.topUp_of :
    UpperTheory.Gal.Wt.TopUp := by
  intro a κ b hb
  have hbt : (b : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := fun i j h => hb i j h
  have hdiag : ∀ i, (b : Matrix (Fin a) (Fin a) ℂ) i i ≠ 0 := by
    have hdet : (b : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
    rw [Matrix.det_of_upperTriangular hbt] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  let t : Fin a → ℂˣ := fun i => Units.mk0 _ (hdiag i)
  set D := diagGL ℂ a t with hD
  set u := D⁻¹ * b with hu
  have hbu : b = D * u := by rw [hu, mul_inv_cancel_left]
  have hDinv : ((D⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal fun i => (((t i)⁻¹ : ℂˣ) : ℂ) := rfl
  have hucoe : (u : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal (fun i => (((t i)⁻¹ : ℂˣ) : ℂ)) * (b : Matrix (Fin a) (Fin a) ℂ) := by
    rw [hu, Units.val_mul, hDinv]
  have hut : (u : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := by
    rw [hucoe]
    exact (Matrix.blockTriangular_diagonal _).mul hbt
  have hu1 : ∀ i, (u : Matrix (Fin a) (Fin a) ℂ) i i = 1 := by
    intro i
    rw [hucoe, Matrix.diagonal_mul]
    simp [t, hdiag i]
  have hfix : (sqRep ℂ a κ u) (top κ) = top κ := by
    apply Subtype.ext
    exact (factSqHighestWeight ℂ a κ).2 u hut hu1
  have hscal : (sqRep ℂ a κ D) (top κ) = chi κ b • top κ := by
    apply Subtype.ext
    have h := (factSqHighestWeight ℂ a κ).1 t
    have hc : (((∏ i, t i ^ κ.w i : ℂˣ)) : ℂ) = chi κ b := by
      rw [Units.coe_prod]
      simp only [Units.val_zpow_eq_zpow_val, chi, t, Units.val_mk0]
    rw [hc] at h
    exact h
  calc (sqRep ℂ a κ b) (top κ) = (sqRep ℂ a κ D) ((sqRep ℂ a κ u) (top κ)) := by
        rw [hbu, map_mul, Module.End.mul_apply]
    _ = chi κ b • top κ := by rw [hfix, hscal]
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.qR_of :
    UpperTheory.Gal.Wt.QR := by
  intro a y
  obtain ⟨k, hk, b, hg, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular (y : Matrix (Fin a) (Fin a) ℂ) y.isUnit
  let u : Matrix.unitaryGroup (Fin a) ℂ := ⟨k, hk⟩
  have hu : ((unitaryIncl a u : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = k := rfl
  refine ⟨u, (unitaryIncl a u)⁻¹ * y, ?_, (mul_inv_cancel_left _ _).symm⟩
  have hbm : (((unitaryIncl a u)⁻¹ * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = b := by
    rw [Units.val_mul, hg, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  intro i j hij
  rw [hbm]
  exact hb hij
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.wExp_h : ExpBasic → SqExp → TorFacts → WExp := by
  intro hB hS hT E _ _ _ a τ W
  classical
  obtain ⟨-, -, hmono, -, -, hinv⟩ := hB
  set v₀ := InfinitePlace.mk τ with hv₀
  let d : ℕ := ∑ i, ((W v₀).w i).natAbs + a * (W v₀).detShift.natAbs
  have hps : ∀ k, psum (W v₀) k ≤ d := fun k => by
    have h1 : psum (W v₀) k ≤ ∑ i, (((W v₀).w i).natAbs : ℤ) :=
      (Finset.sum_le_sum fun i _ => Int.le_natAbs).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _)
    have h2 : (0 : ℤ) ≤ ((a * (W v₀).detShift.natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
    simp only [d, Nat.cast_add, Nat.cast_sum]
    omega
  have h1 : ∀ k w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ), (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpGe (-d) := fun k w L =>
    ⟨(hmono _ _ (hps k)).1 (hS a k _ w L).1, (hmono _ _ (neg_le_neg (by exact_mod_cast Nat.le_add_left _ _))).2 (hS a k _ w L).2⟩
  refine ⟨d, fun k x hx v L => ?_⟩
  have h2 : (∀ z, (x z).1 ∈ embU a v₀.embedding) ∧ ∀ w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ),
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpGe (-d) := by
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · rw [hv₀, e]
      refine ⟨fun z => (hx z).1, fun w L => ?_⟩
      simp only [(hx _).2]
      exact h1 k w L
    · rw [hv₀, e]
      refine ⟨fun z => by rw [GlobalTheory.DefiniteBC.embU_conjugate]; exact (hx z).1, fun w L => ?_⟩
      have e2 : ∀ z, cEmb (ComplexEmbedding.conjugate τ) (x z).1 = tor a k z⁻¹ := fun z => by
        rw [← (hT a k z).2.2.2, ← (hx z).2]
        ext i j
        simp [cEmb, GlobalTheory.DefiniteBC.coord_conjugate]
      simp only [e2]
      have h3 := (hinv _ _).2 (h1 k w L).2
      rw [neg_neg] at h3
      exact ⟨h3, (hinv _ _).1 (h1 k w L).1⟩
  let Φ : W.Sp →ₗ[ℂ] (Circle → ℂ) := LinearMap.pi fun z => L ∘ₗ W.rep (x z)
  let N : Submodule ℂ W.Sp := (ExpLe d ⊓ ExpGe (-d)).comap Φ
  have hN : ∀ e, GlobalTheory.CoefIrred.tenMul W e ∈ N := fun e => by
    have h := h2.2 (e v₀) (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
    have e3 : Φ (GlobalTheory.CoefIrred.tenMul W e) = fun z => (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
        (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) (e v₀)) := by
      funext z
      have := rep_tenMul_update W v₀ (x z) (h2.1 z) e (e v₀)
      rw [Function.update_eq_self] at this
      exact congrArg L this
    change Φ _ ∈ ExpLe d ⊓ ExpGe (-d)
    rw [e3]
    exact h
  have h0 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) a W (W.Sp ⧸ N) 0).unique (y₁ := N.mkQ) (y₂ := 0)
    (fun u => (Submodule.Quotient.mk_eq_zero N).2 (hN u)) (fun u => rfl)
  exact (Submodule.Quotient.mk_eq_zero N).1 (LinearMap.congr_fun h0 v)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.autCrit_of :
    UpperTheory.Gal.Wt.AutCrit := by
  intro E _ _ _ a C hLev φ hL hC hI S hS hSub
  obtain ⟨N, hNo, hN1, hNC⟩ := hLev.isOpen
  set Wn : Set (UA E a) := GlobalTheory.EllU.finPart ⁻¹' N with hWn
  have hWo : IsOpen Wn := hNo.preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E a) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ N
    rw [map_one]; exact hN1
  have hkey : ∀ g, ∀ w ∈ Wn, φ (g * w) = φ (g * ((GlobalTheory.EllU.finPart w)⁻¹ * w)) := by
    intro g w hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hNC ⟨hw, GlobalTheory.EllU.finPart_mem w⟩
    have hx := GlobalTheory.EllU.inv_finPart_mul_mem w
    have hcm := GlobalTheory.DefU.fin_mul_inf (GlobalTheory.EllU.finPart_mem w) hx
    have e : g * w = g * ((GlobalTheory.EllU.finPart w)⁻¹ * w) * GlobalTheory.EllU.finPart w := by
      rw [mul_assoc, ← hcm]; group
    rw [e, hC _ hkC]
  refine ⟨?_, hL, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    have hc : Continuous fun y : UA E a => g⁻¹ * y := continuous_const.mul continuous_id
    have hX : Continuous fun y : UA E a => (⟨(GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y),
        GlobalTheory.EllU.inv_finPart_mul_mem _⟩ : infU E a) :=
      Continuous.subtype_mk (((GlobalTheory.EllU.continuous_finPart.comp hc).inv).mul hc) _
    have h0 : ContinuousAt (fun y : UA E a => φ (g * ((GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y)))) g :=
      ((hI g).comp hX).continuousAt
    refine h0.congr ?_
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    have := hkey g _ hy
    rw [mul_inv_cancel_left] at this
    exact this.symm
  · refine GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds ((RU E a).comp (finU E a).subtype) _ ?_
    have ho : IsOpen ((Subtype.val : finU E a → UA E a) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    have hk' : (k : UA E a) ∈ C := by
      refine hNC ⟨?_, k.2⟩
      have : GlobalTheory.EllU.finPart (k : UA E a) ∈ N := hk
      rwa [GlobalTheory.EllU.finPart_of_finU k.2] at this
    funext g
    exact hC _ hk' g
  · haveI := hS
    refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hSub k k.2
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem RU_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (x : UA E a) (φ ψ : UA E a → ℂ) :
    RU E a x (fun g => φ g * ψ g) = RU E a x φ * RU E a x ψ := by
  ext g
  rfl

theorem UpperTheory.Gal.Wt.autMul_of :
    UpperTheory.Gal.Wt.AutMul := by
  intro E _ _ _ a φ ψ hφ hψ
  refine ⟨hφ.cont.mul hψ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change φ (γ * g) * ψ (γ * g) = φ g * ψ g
    rw [hφ.left γ hγ, hψ.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E a).comp (finU E a).subtype) (fun g => φ g * ψ g) ?_
    refine Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E a 1 φ = φ
      simp
    · change RU E a 1 ψ = ψ
      simp
    · have h1 : RU E a k φ = φ := hk.1
      have h2 : RU E a k ψ = ψ := hk.2
      change RU E a k (fun g => φ g * ψ g) = fun g => φ g * ψ g
      rw [RU_mul', h1, h2]
      rfl
  · haveI := hφ.kfin
    haveI := hψ.kfin
    have f1 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    have f2 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) :=
      Submodule.fg_iff_finiteDimensional _ |>.1 (f1.mul f2)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E a k (fun g => φ g * ψ g) ∈ _
    rw [RU_mul']
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.nrmAut_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.NrmAut := by
  intro hC E _ _ _ a τ C hCl n hn p hp
  obtain ⟨hpc, A, hAf, hA⟩ := hp
  let S : Submodule ℂ (UA E a → ℂ) := A.map (LinearMap.funLeft ℂ ℂ n)
  have hSf : FiniteDimensional ℂ S := inferInstance
  have hS : ∀ y, (fun g => p (n g * y)) ∈ S := fun y => ⟨_, hA y, rfl⟩
  refine ⟨fun y => ?_, S, hSf, hS⟩
  refine hC E a C hCl _ (fun γ hγ g => by simp only [hn.left γ hγ g])
    (fun c hc g => by simp only [hn.lev c hc g]) (fun g => ?_) S hSf (fun x hx => ?_)
  · have he : (fun x : infU E a => p (n (g * x.1) * y)) =
        fun x : infU E a => p (n g * (cEmb τ x.1 * y)) := by
      funext x
      rw [hn.inf x.1 x.2 g, mul_assoc]
    rw [he]
    exact hpc.comp (continuous_const.mul
      (((GlobalTheory.AutRec.continuous_cEmb_emb τ).comp continuous_subtype_val).mul continuous_const))
  · have he : RU E a x (fun g => p (n g * y)) = fun g => p (n g * (cEmb τ x * y)) := by
      funext g
      change p (n (g * x) * y) = _
      rw [hn.inf x hx g, mul_assoc]
    rw [he]
    exact hS _
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.famOfA_of :
    UpperTheory.Gal.Wt.AutMul → UpperTheory.Gal.Wt.NrmAut → UpperTheory.Gal.Wt.RFinEx → UpperTheory.Gal.Wt.FamOfA := by
  intro hMul hNrm hR E _ _ _ a τ C hC n hn W ν Q _ f P X
  have hp := fun q => hNrm E a τ C hC n hn (pev (P q)) ((hR a).2 (P q))
  have hd := fun q => hNrm E a τ C hC n hn (fun m => delta ν (X q * m)) ((hR a).1 ν (X q))
  have key : ∀ y₁ y₂ v, famOf n ν f P X y₁ y₂ v =
      ∑ q, ((fun g => pev (P q) (n g * y₂)) * (fun g => delta ν (X q * (n g * y₁)))) * (f q).1 v := by
    intro y₁ y₂ v
    funext g
    rw [famOf_apply, Finset.sum_apply]
    rfl
  refine ⟨fun y₁ y₂ v => ?_, ?_⟩
  · rw [key]
    exact mem_autU.1 (Submodule.sum_mem _ fun q _ => mem_autU.2
      (hMul E a _ _ (hMul E a _ _ ((hp q).1 y₂) ((hd q).1 y₁)) ((f q).2.1 v)))
  · choose S₁ hS₁f hS₁ using fun q => (hp q).2
    choose S₂ hS₂f hS₂ using fun q => (hd q).2
    have hfin : ∀ q, FiniteDimensional ℂ ↥(S₁ q * S₂ q * LinearMap.range (f q).1) := fun q => by
      have h₁ : (S₁ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₁f q)
      have h₂ : (S₂ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₂f q)
      have h₃ : (LinearMap.range (f q).1).FG := Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
      exact Submodule.fg_iff_finiteDimensional _ |>.1 ((h₁.mul h₂).mul h₃)
    refine ⟨⨆ q, S₁ q * S₂ q * LinearMap.range (f q).1, Submodule.finiteDimensional_iSup _, ?_⟩
    intro y₁ y₂ v
    rw [key]
    exact Submodule.sum_mem _ fun q _ => Submodule.mem_iSup_of_mem q
      (Submodule.mul_mem_mul (Submodule.mul_mem_mul (hS₁ q y₂) (hS₂ q y₁)) (LinearMap.mem_range_self _ v))
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.sumRep_of :
    UpperTheory.Gal.Wt.SumRep := by
  intro E _ _ _ a S hfin hS
  classical
  obtain ⟨B₀, -, -, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E a
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (autU E a).subtype (autU E a).ker_subtype
  have hpv : ∀ (φ : UA E a → ℂ) (h : IsAutFormU φ), p φ = ⟨φ, h⟩ := fun φ h =>
    LinearMap.congr_fun hp (⟨φ, h⟩ : autU E a)
  let B : (UA E a → ℂ) →ₗ⋆[ℂ] (UA E a → ℂ) →ₗ[ℂ] ℂ := (B₀.compl₂ p).comp p
  have hB : ∀ φ φ', B φ φ' = B₀ (p φ) (p φ') := fun _ _ => rfl
  have hsum : ∀ φ : UA E a → ℂ, IsAutFormU φ → φ ∈ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U} := by
    intro φ hφ
    have h := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E a B (fun f hf h0 => by
        rw [hB, hpv f hf] at h0
        exact congrArg Subtype.val (hd _ h0))
      (fun x f g hf hg => by
        rw [hB, hB, hpv f hf, hpv g hg, hpv _ (RU_mem_autU x f hf), hpv _ (RU_mem_autU x g hg)]
        exact hi x ⟨f, hf⟩ ⟨g, hg⟩) φ hφ
    exact (iSup_le fun σ => le_sSup σ.2 : _ ≤ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) h
  let b := Module.finBasis ℂ S
  have hex : ∀ i, ∃ s : Finset (Submodule ℂ (UA E a → ℂ)), (↑s ⊆ {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) ∧
      (b i : UA E a → ℂ) ∈ ⨆ U ∈ s, U :=
    fun i => Submodule.mem_sSup_iff_exists_finset.1 (hsum _ (hS _ (b i).2))
  choose s hsA hsm using hex
  let s0 := Finset.univ.biUnion s
  have hs0A : ∀ U ∈ s0, IsAutRepU U := by
    intro U hU
    obtain ⟨i, -, hi'⟩ := Finset.mem_biUnion.1 hU
    exact hsA i hi'
  obtain ⟨t, hts, hti, htS⟩ := GlobalTheory.EigenDecomp.exists_indep s0 hs0A
  refine ⟨t, fun U hU => hs0A U (hts hU), hti, ?_⟩
  intro φ hφ
  rw [htS]
  have e : φ = ∑ i, (b.repr ⟨φ, hφ⟩ i) • (b i : UA E a → ℂ) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine (iSup₂_le fun U hU => le_sSup ?_ : (⨆ U ∈ s i, U) ≤ sSup (s0 : Set (Submodule ℂ (UA E a → ℂ)))) (hsm i)
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hU⟩)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.neatLev_of :
    UpperTheory.Gal.Wt.NeatLev := by
  intro E _ _ _ l hl a ha w₀ hmem hs v' hv' hap K hK hint Kv hKv W f hf
  obtain ⟨N, hN, hNf⟩ := UpperTheory.Gal.Gen.smoothAt_holds E a w₀ hs W f
  obtain ⟨J, hJ, hJN, hJt, -⟩ := UpperTheory.Gal.Gen.tower_holds E w₀ a l hl hmem ha N hN
  obtain ⟨hLev, hmemC, hcJ, -, -, -⟩ :=
    UpperTheory.Gal.Gen.levFacts_holds E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hKC : K ≤ UpperTheory.Gal.Gen.lev K w₀ (J 0) := le_sup_left
  refine ⟨UpperTheory.Gal.Gen.lev K w₀ (J 0), hLev, hKC, ?_, ?_, ?_⟩
  · intro g γ hγ c hc x hx h
    have hT : UpperTheory.Gal.CharacterCongruences.TorsFreeAt (UpperTheory.Gal.Gen.lev K w₀ (J 0)) w₀ :=
      fun k hk ho => hJt _ (hcJ k hk) ho
    exact UpperTheory.Gal.CharacterCongruences.neatOfPlace_holds E a _ ⟨hLev.fin, hLev.compact, hLev.isOpen⟩ w₀ hT
      g γ hγ c hc x hx h
  · have hKGL : GlobalTheory.LFun.KGL v' a ≤ (UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v') := by
      intro y hy
      obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a v' hv'
      have hy' : cLoc v' (e.symm y : UA E a) = y := by rw [← he]; simp
      exact ⟨(e.symm y : UA E a), hKC (hint _ (e.symm y).2 (hy'.symm ▸ hy)), hy'⟩
    have hmax := UpperTheory.Gal.Gen.maxCpt_holds E v' a ((UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v'))
      (cLoc v' '' (UpperTheory.Gal.Gen.lev K w₀ (J 0) : Set (UA E a)))
      (hLev.compact.image (GlobalTheory.BCT.GlobLev.continuous_cLoc v'))
      (fun _ h => h) hKGL
    intro c hc
    exact hmax ⟨c, hc, rfl⟩
  · intro c hc v g
    obtain ⟨hcC, hcv⟩ := hc
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (hmemC _).1 hcC
    have hx1 : cLoc v' x = 1 :=
      MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v') hap)
    have hkv : k ∈ K ⊓ Kv.comap (cLoc v') := by
      refine ⟨hk, ?_⟩
      have h2 : cLoc v' (k * x) ∈ Kv := hcv
      rw [map_mul, hx1, mul_one] at h2
      exact h2
    rw [← mul_assoc, hNf x hx (hJN hxJ) v (g * k)]
    exact hf k hkv v g
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.ellC_of :
    UpperTheory.Gal.Wt.EllC := by
  intro E _ _ _ a C hC hneat
  set D : Subgroup (UA E a) := C ⊔ infU E a with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  have hyp : ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ d : D, γ * g = g * d → f d = 1 := by
    intro g γ hγ d h
    have hfd : GlobalTheory.EllU.finPart (d : UA E a) ∈ C := hDC d.2
    have e : γ * g = g * GlobalTheory.EllU.finPart (d : UA E a) * ((GlobalTheory.EllU.finPart (d : UA E a))⁻¹ * (d : UA E a)) := by
      rw [h]; group
    have h1 := hneat g γ hγ _ hfd _ (GlobalTheory.EllU.inv_finPart_mul_mem (d : UA E a)) e
    exact Subtype.ext h1
  obtain ⟨ℓ, h1, h2⟩ := UpperTheory.Gal.Gen.ellGrp_holds (UA E a) C (ratU E a) D f hyp
  have hinf : ∀ x ∈ infU E a, ∀ g, ℓ (g * x) = ℓ g := by
    intro x hx g
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [e, mul_one] at this
    exact this
  have hC' : ∀ (c : C) g, ℓ (g * c) = ℓ g * c := by
    intro c g
    have e : f ⟨c, le_sup_left (b := infU E a) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E a) c.2⟩
    simp only [e] at this
    exact this
  exact ⟨ℓ, ⟨h1, hC', hinf⟩⟩
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.twist_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.Twist := by
  intro hA E _ _ _ a C hC ℓ hℓ W f c
  let e : UA E a → UA E a := fun g => (((ℓ g)⁻¹ * c : C) : UA E a)
  have he : ∀ g, e g ∈ finU E a := fun g => hC.fin ((ℓ g)⁻¹ * c).2
  let F : W.Sp →ₗ[ℂ] (UA E a → ℂ) :=
    { toFun := fun v g => f.1 v (g * e g)
      map_add' := fun v w => by funext g; simp
      map_smul' := fun r v => by funext g; simp }
  have hF : ∀ v g, F v g = f.1 v (g * e g) := fun _ _ => rfl
  have hleft : ∀ γ ∈ ratU E a, ∀ v g, F v (γ * g) = F v g := by
    intro γ hγ v g
    have h : e (γ * g) = e g := by simp only [e, hℓ.left γ hγ g]
    rw [hF, hF, h, mul_assoc]
    exact (f.2.1 v).left γ hγ _
  have hlev : ∀ k ∈ C, ∀ v g, F v (g * k) = F v g := by
    intro k hk v g
    have h : g * k * e (g * k) = g * e g := by
      simp only [e, hℓ.lev ⟨k, hk⟩ g, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hF, hF, h]
  have hinf : ∀ x ∈ infU E a, ∀ v g, F v (g * x) = f.1 v (g * x * e g) := by
    intro x hx v g
    have h : e (g * x) = e g := by simp only [e, hℓ.inf x hx g]
    rw [hF, h]
  have heqv : ∀ (x : infU E a) v, F (W.rep x v) = RU E a x (F v) := by
    intro x v
    funext g
    rw [RU_apply, hinf x x.2, hF, f.2.2 x v, RU_apply, mul_assoc g, mul_assoc g, fin_mul_inf (he g) x.2]
  have haut : ∀ v, IsAutFormU (F v) := by
    intro v
    refine hA E a C hC (F v) (fun γ hγ g => hleft γ hγ v g) (fun k hk g => hlev k hk v g) ?_
      (LinearMap.range F) inferInstance fun x hx => ⟨W.rep ⟨x, hx⟩ v, heqv ⟨x, hx⟩ v⟩
    intro g
    have h : (fun x : infU E a => F v (g * x)) = fun x : infU E a => f.1 v (g * x * e g) :=
      funext fun x => hinf x x.2 v g
    rw [h]
    exact (f.2.1 v).cont.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  exact ⟨⟨F, haut, heqv⟩, UpperTheory.Gal.Gen.mem_fixedBy.2 fun k hk v g => hlev k hk v g, fun _ _ => rfl⟩
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)

namespace UpperTheory.Gal.Wt

private theorem isOpen_subgroupOf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    {C C₀ : Subgroup (UA E a)} (hC : IsLevel C) (hC₀ : IsLevel C₀) :
    IsOpen ((C₀.subgroupOf C : Subgroup C) : Set C) := by
  obtain ⟨N, hNo, h1N, hNC⟩ := hC₀.isOpen
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  refine Filter.mem_of_superset
    ((hNo.preimage continuous_subtype_val).mem_nhds (show ((1 : C) : UA E a) ∈ N from h1N)) ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, hC.fin x.2⟩)

theorem twistBd_of : Twist → TwistBd := by
  intro hT E _ _ _ l _ ι a C hC ℓ hℓ W f X b hb
  classical
  obtain ⟨C₀, hC₀, hf⟩ := UpperTheory.Gal.Gen.levelEx_holds E a W f
  have hHo := isOpen_subgroupOf hC hC₀
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  haveI : Finite (C ⧸ C₀.subgroupOf C) := Subgroup.quotient_finite_of_isOpen _ hHo
  letI := Fintype.ofFinite (C ⧸ C₀.subgroupOf C)
  have hq : ∀ q : C ⧸ C₀.subgroupOf C, ∃ R : ℝ, ∀ g i,
      ‖ι.symm (f.1 (b g i) (g * ((ℓ g)⁻¹ * q.out : C)))‖ ≤ R := by
    intro q
    obtain ⟨F, -, hF⟩ := hT E a C hC ℓ hℓ W f q.out
    obtain ⟨R, hR⟩ := hb F
    exact ⟨R, fun g i => by rw [← hF]; exact hR g i⟩
  choose R hR using hq
  refine ⟨1 + ∑ q, |R q|, by positivity, fun c g i => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (C₀.subgroupOf C) c
  have hhC : ((h : C) : UA E a) ∈ C₀ := Subgroup.mem_subgroupOf.1 h.2
  have e : f.1 (b g i) (g * ((ℓ g)⁻¹ * (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C).out : C)) =
      f.1 (b g i) (g * ((ℓ g)⁻¹ * c : C)) := by
    rw [hh]
    have : (((ℓ g)⁻¹ * (c * (h : C)) : C) : UA E a) = (((ℓ g)⁻¹ * c : C) : UA E a) * ((h : C) : UA E a) := by
      simp [mul_assoc]
    rw [this, ← mul_assoc]
    exact hf _ hhC _ _
  rw [← e]
  refine (hR _ g i).trans ((le_abs_self _).trans ?_)
  have := Finset.single_le_sum (f := fun q => |R q|) (fun q _ => abs_nonneg _)
    (Finset.mem_univ (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C))
  linarith

end UpperTheory.Gal.Wt

end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.kapl_of :
    UpperTheory.Gal.Wt.KaplFin → UpperTheory.Gal.Wt.Kapl := by
  intro hfin k _ _ Y hY δ ε hδ hε hε1
  have hY' : IsCompact (Y ∩ {x : k | δ ≤ ‖x‖}) :=
    hY.inter_right (isClosed_le continuous_const continuous_norm)
  have hnhds : ∀ c ∈ Y ∩ {x : k | δ ≤ ‖x‖}, Metric.closedBall c (‖c‖ / 2) ∈ nhds c := by
    intro c hc
    have hc' : δ ≤ ‖c‖ := hc.2
    exact Metric.closedBall_mem_nhds c (by linarith)
  obtain ⟨s, hs, hcov⟩ := hY'.elim_nhds_subcover (fun c => Metric.closedBall c (‖c‖ / 2)) hnhds
  obtain ⟨p, h1, h2, h3⟩ := hfin k s δ ε hδ hε hε1 (fun c hc => (hs c hc).2)
  have hbig : ∀ x ∈ Y, δ ≤ ‖x‖ → ‖p.eval x‖ ≤ ε := by
    intro x hx hxδ
    have hmem := hcov ⟨hx, hxδ⟩
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨c, hc, hxc⟩ := hmem
    exact h2 c hc x (by simpa [dist_eq_norm] using hxc)
  refine ⟨p, fun x hx => ?_, hbig, h3⟩
  rcases le_total ‖x‖ δ with h | h
  · exact h1 x h
  · exact (hbig x hx h).trans hε1
end

section
namespace UpperTheory.Gal.Wt

theorem expBasic_holds : ExpBasic := expBasic_of
theorem expDisj_holds : ExpDisj := expDisj_of
theorem evLem_holds : EvLem := evLem_of
theorem pevExp_holds : PevExp := pevExp_of expBasic_holds
theorem dom_holds : Dom := dom_of
theorem sqExp_holds : SqExp := sqExp_h expBasic_holds evLem_holds dom_holds
theorem topUp_holds : TopUp := topUp_of
theorem torFacts_holds : TorFacts := torFacts_of
theorem qR_holds : QR := qR_of
theorem wtBd_holds : WtBd := wtBd_of expBasic_holds expDisj_holds sqExp_holds topUp_holds torFacts_holds
theorem wExp_holds : WExp := wExp_h expBasic_holds sqExp_holds torFacts_holds
theorem rFinEx_holds : RFinEx := rFinEx_of
theorem deltaNear_holds : DeltaNear := deltaNear_h
theorem autCrit_holds : AutCrit := autCrit_of
theorem autMul_holds : AutMul := autMul_of
theorem nrmAut_holds : NrmAut := nrmAut_of autCrit_holds
theorem famOfA_holds : FamOfA := famOfA_of autMul_holds nrmAut_holds rFinEx_holds
theorem sumRep_holds : SumRep := sumRep_of
theorem neatLev_holds : NeatLev := neatLev_of
theorem ellC_holds : EllC := ellC_of
theorem twist_holds : Twist := twist_of autCrit_holds
theorem twistBd_holds : TwistBd := twistBd_of twist_holds
theorem ladic_weight_embedding_over_place : Kap0 := ladic_weight_at_embedding_over_place
theorem kaplFin_holds : KaplFin := kaplFin_of
theorem kapl_holds : Kapl := kapl_of kaplFin_holds
theorem sepPoly_holds : SepPoly := sepPoly_of kapl_holds
theorem nearSub_holds : NearSub := nearSub_of
theorem pieces_holds : Pieces := pieces_of sepPoly_holds nearSub_holds
theorem famOf_holds : FamOf := famOf_of expBasic_holds pevExp_holds sqExp_holds topUp_holds wExp_holds famOfA_holds
theorem famEx_holds : FamEx := famEx_of neatLev_holds ellC_holds twist_holds twistBd_holds ladic_weight_embedding_over_place pieces_holds deltaNear_holds famOf_holds
theorem famProj_holds : FamProj := famProj_of evLem_holds sumRep_holds
theorem famSum_holds : FamSum := famSum_of expBasic_holds evLem_holds torFacts_holds qR_holds wtBd_holds embProj_holds
theorem famWt_holds : FamWt := famWt_of famOff_holds famSum_holds

theorem wtLacEx_holds : UpperTheory.Gal.Int.Cong.WtLacEx := top_of famEx_holds famProj_holds famWt_holds

end UpperTheory.Gal.Wt
end
