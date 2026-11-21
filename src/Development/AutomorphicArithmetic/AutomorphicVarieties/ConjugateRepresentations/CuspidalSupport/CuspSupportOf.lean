import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.TensEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TwoVar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SumInner
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MatBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatOfEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Gl2LocalToAdelicEmbedding
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TauSat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TypesComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HullBdd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SingleBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SliceBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LocComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MemFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.PairEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppCusp

section
open Polynomial

namespace UpperTheory.V.Cj.S

private theorem eq_of_prod_eq (m n : Multiset ℂ) (h : ∀ u : ℂ, (m.map (u + ·)).prod = (n.map (u + ·)).prod) : m = n := by
  have key : ∀ (k : Multiset ℂ) (u : ℂ),
      (((k.map fun x => -x).map fun x => X - C x).prod).eval u = (k.map (u + ·)).prod := by
    intro k u
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp
  have hp : ((m.map fun x => -x).map fun x => X - C x).prod = ((n.map fun x => -x).map fun x => X - C x).prod :=
    Polynomial.funext fun u => by rw [key, key, h]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem capArith : CapArith := by
  intro m m₁ m₂ α β h
  refine eq_of_prod_eq _ _ fun u => ?_
  rw [← h u, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring

end UpperTheory.V.Cj.S
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.levelSplit :
    UpperTheory.V.Cj.S.LevelSplit := by
  intro E _ _ a L hL
  have ho : IsOpen ((L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := hL.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hev := LocSph.eventually_mem (ho.mem_nhds (one_mem _))
  refine ⟨_, ho, inf_le_left, _, Filter.eventually_cofinite.1 hev, fun w hw => ?_⟩
  have hw' := not_not.1 hw
  have h1 : ∀ k ∈ KGL w a, locGL E a w k ∈ L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a := by
    rintro _ ⟨g, rfl⟩
    exact hw' g
  refine ⟨h1, fun u hu => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w) u ∈ KGL w a := by
    obtain ⟨h2, h3⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E a).1 hu.2
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h2 i j w
    · rw [← map_inv]
      exact h3 i j w
  exact ⟨_, hk, _, mul_mem (inv_mem (h1 _ hk)) hu, LocEx.map_pLoc_inv_mul w u, (mul_inv_cancel_left _ _).symm⟩
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.capOfEig :
    UpperTheory.V.Cj.S.CapOfEig := by
  intro E _ _ _ a φ h0 hc
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have key : ∀ t : E →+* ℂ, ∃ m : Multiset ℂ, Multiset.card m = a ∧
      ∀ u : ℂ, cap t u φ = (m.map (u + ·)).prod • φ := fun t => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.CuspRep.exists_multiset_qdet (Eop (a := a) t) (((a : ℂ) - 1) / 2) φ f hf
    refine ⟨m, hm, fun u => ?_⟩
    obtain ⟨c, h1⟩ := hc t u
    have h2 : f (cap t u φ) = _ := h u
    rw [h1, map_smul, hf, smul_eq_mul, mul_one] at h2
    rw [h1, h2]
  choose m hm h using key
  exact ⟨m, fun t => ⟨hm t, h t⟩⟩
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

open UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem hull_stable {T : Module.End ℂ (Sm E a)} (hT : T ∈ Comm E a) (S : Submodule ℂ (Sm E a)) :
    ∀ φ ∈ hull S, T φ ∈ hull S := by
  have : hull S ≤ (hull S).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨T', hT', φ, hφ, rfl⟩
    exact Submodule.subset_span ⟨T * T', ⟨fun k => (hT.1 k).mul_left (hT'.1 k),
      fun z hz => (hT.2.1 z hz).mul_left (hT'.2.1 z hz), fun ψ h => hT.2.2 _ (hT'.2.2 ψ h)⟩, φ, hφ, rfl⟩
  exact fun φ hφ => this hφ

private theorem aut_cap (t : E →+* ℂ) (u : ℂ) (φ : Sm E a) (h : IsAutForm φ) : IsAutForm (cap t u φ) := by
  obtain ⟨p, -, q, -, e⟩ := Cm.mem_Zalg_iff.1 (Cm.cap_mem_Zalg (a := a) t u)
  obtain ⟨ψ, rfl⟩ := Cm.mem_range_ofAut.2 h
  refine Cm.mem_range_ofAut.1 ⟨GroundTheory.Automorphic.AutomorphicForm.uActionAF E a p ψ +
    Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E a q ψ, ?_⟩
  rw [e, map_add, map_smul]
  rfl

private theorem smEq_fin (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    Cm.smEq E a (finRep E a g φ) = GroundTheory.Automorphic.AutomorphicForm.rtFin g (Cm.smEq E a φ) :=
  Subtype.ext (funext fun x => (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (x * f g)) Fb.finEmb_eq).symm)

private theorem fin_mem (g : GL (Fin a) (Af E)) : finRep E a g ∈ Comm E a := by
  refine ⟨fun k => ?_, fun z _ => ?_, fun φ h => ?_⟩
  · exact Commute.map (show Commute (finGL E a g) (infGL E a (Unitary.toUnits k)) from (infGL_comm _ _).symm) (rt E a)
  · refine LinearMap.ext fun φ => (Cm.smEq E a).injective ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, smEq_fin, Cm.smEq_uTC, Cm.smEq_uTC, smEq_fin,
      GroundTheory.Automorphic.AutomorphicForm.uAction_rtFin]
  · refine (Cm.isAutForm_iff _).2 ?_
    rw [← Cm.coe_smEq, smEq_fin]
    exact ((Cm.isAutForm_iff _).1 h).rightTranslate_finEmb g

end

theorem UpperTheory.V.Cj.S.hullOps :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.HullOps := by
  intro hc E _ _ _ a S
  refine ⟨fun φ hφ => Submodule.subset_span ⟨1, ⟨fun _ => Commute.one_left _, fun _ _ => Commute.one_left _,
    fun _ h => h⟩, φ, hφ, rfl⟩, fun t u => hull_stable ⟨fun k => (hc E a t u).2.1 (.cpt k),
      fun z _ => (hc E a t u).2.2.1 z, aut_cap t u⟩ S, fun g => hull_stable (fin_mem g) S⟩
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.stabSp :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.LevelSplit → UpperTheory.V.Cj.S.HullBdd → UpperTheory.V.Cj.S.HullOps → UpperTheory.V.Cj.S.StabSp := by
  intro hC hL hB hO E _ _ _ a S hS
  obtain ⟨L, hLo, hl⟩ := hS.level
  obtain ⟨L', hL'o, hle, T, hT, hsp⟩ := hL E a L hLo
  obtain ⟨h1, h2, h3⟩ := hO E a S
  have hb := hB E a S hS L' hL'o
  have hK : ∀ w ∉ T, fixed (finRep E a) L' ≤ fixed (fL a w) (KGL w a) := fun w hw φ hφ =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ _ ((hsp w hw).1 k hk)
  refine ⟨T, hT, hull S ⊓ fixed (finRep E a) L', le_inf h1 fun φ hφ => ?_, ?_, fun φ hφ => ?_,
    fun w hw => inf_le_right.trans (hK w hw), ?_⟩
  · refine GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (funext fun g => ?_)
    have := hl _ ⟨φ, hφ, rfl⟩ u (hle hu) g
    rw [UpperTheory.V.Fb.finEmb_eq] at this
    exact this
  · haveI := UpperTheory.V.Af.Fin.formsFinite E a _ hb
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (UpperTheory.V.Cm.smEq E a).injective _).symm
  · exact (UpperTheory.V.Cm.isAutForm_iff φ).2 (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hb _ ⟨φ, hφ, rfl⟩)
  · rintro (⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩) φ ⟨hφ, hφ'⟩
    · refine ⟨h2 t u φ hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
      have e := LinearMap.congr_fun ((hC E a t u).1 (finGL E a k)).eq φ
      have e' : rt E a (finGL E a k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ' k hk
      rw [Module.End.mul_apply, Module.End.mul_apply, e'] at e
      exact e.symm
    · have hc := Final.GLintComm E w a
      refine ⟨?_, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
      · change heckeVec (fL a w) (KGL w a) h φ ∈ hull S
        rw [heckeVec, finsum_eq_sum (fun c : _ ⧸ KGL w a => h c.out • fL a w c.out φ) (finite_heckeVec hc hh (fL a w) φ)]
        exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (h3 _ φ hφ)
      · change finRep E a u (heckeVec (fL a w) (KGL w a) h φ) = heckeVec (fL a w) (KGL w a) h φ
        obtain ⟨k, hk, u', hu', e1, rfl⟩ := (hsp w hw).2 u hu
        have e2 := map_heckeVec hc hh (ρ := fL a w) (ρ' := fL a w) (finRep E a u') (fun g y => by
          change finRep E a u' (finRep E a (locGL E a w g) y) = finRep E a (locGL E a w g) (finRep E a u' y)
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
            LocUniq.comm_locGL w e1]) φ
        rw [map_mul, Module.End.mul_apply, e2, GlobalTheory.LGrp.mem_fixed.1 hφ' u' hu']
        exact GlobalTheory.LGrp.mem_fixed.1 (SatCompare.heckeVec_mem_fixed hc hh (hK w hw hφ')) k hk
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem hk_comm_of {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {K : Subgroup G} (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (A : Module.End ℂ V)
    (hA : ∀ g, Commute A (ρ g)) (x : V) : A (hkOp ρ hK hh x) = hkOp ρ hK hh (A x) :=
  map_heckeVec hK hh (ρ' := ρ) A (fun g y => LinearMap.congr_fun (hA g).eq y) x

theorem UpperTheory.V.Cj.S.opComm :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.OpComm := by
  intro hC E _ _ _ a T i i' φ hφ
  rcases i with ⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩ <;> rcases i' with ⟨t', u'⟩ | ⟨⟨w', hw'⟩, h', hh'⟩
  · exact LinearMap.congr_fun ((hC E a t u).2.2.2 t' u').eq φ
  · exact hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (cap t u) (fun g => (hC E a t u).1 _) φ
  · exact (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (cap t' u') (fun g => (hC E a t' u').1 _) φ).symm
  · by_cases e : w = w'
    · subst e
      have hK := Final.GLintComm E w a
      change heckeVec (fL a w) (KGL w a) h (heckeVec (fL a w) (KGL w a) h' φ) =
        heckeVec (fL a w) (KGL w a) h' (heckeVec (fL a w) (KGL w a) h φ)
      rw [← SatCompare.heckeVec_conv hK hh hh' (hφ w hw), ← SatCompare.heckeVec_conv hK hh' hh (hφ w hw),
        Final.HeckeCommGL E w a ℂ h hh h' hh']
    · refine hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (hkOp (fL a w) (Final.GLintComm E w a) hh)
        (fun g => LinearMap.ext fun y => ?_) φ
      refine (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (fL a w' g) (fun k => ?_) y).symm
      exact Commute.map (LocUniq.comm_locGL w (pLoc_locGL_of_ne e g) k) (finRep E a)
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.iwa :
    UpperTheory.V.Cj.S.RtK → UpperTheory.V.Cj.S.Iwa := by
  intro hK E _ _ _ r s φ m B hφ ⟨g, hg⟩
  obtain ⟨b, hb, k, hk, rfl⟩ := GroundTheory.Automorphic.Reduction.exists_adelicBorel_mul_maxCompact (K := E) (n := r + s) g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (GroundTheory.Automorphic.Reduction.mem_adelicBorel.1 hb)
  refine ⟨_, hK E (r + s) φ m B hφ k hk, m₁, m₂, ?_⟩
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant φ.1 := hφ.aut.left
  rw [mul_assoc, UpperTheory.constantTerm_unipotent_left_invariant E (r + s) r φ.1 hl] at hg
  rw [← GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate] at hg
  exact hg
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctCap :
    UpperTheory.V.Cj.S.CtCap := by
  intro E _ _ _ n r φ hφ
  have ha := (UpperTheory.V.Cm.isAutForm_iff φ).1 hφ
  obtain ⟨f, hf, hfu⟩ := UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping E n r
  let φ' : GroundTheory.Automorphic.AutomorphicForm.automorphicForms E n := ⟨φ.1, ha⟩
  refine ⟨(UpperTheory.V.Cm.smEq E n).symm (f φ'), hf φ', fun X g => ?_, fun t u => ?_⟩
  · rw [UpperTheory.V.Cm.coe_smEq_symm, hf]
    exact UpperTheory.constantTerm_unipotent_left_invariant E n r φ.1 ha.isLeftInvariant X g
  · obtain ⟨p, -, q, -, e⟩ := UpperTheory.V.Cm.mem_Zalg_iff.1 (UpperTheory.V.Cm.cap_mem_Zalg (a := n) t u)
    have h := hf (GroundTheory.Automorphic.AutomorphicForm.uActionAF E n p φ' +
      Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E n q φ')
    rw [map_add, map_smul, hfu, hfu] at h
    rw [e]
    exact h
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctSat :
    UpperTheory.V.Cj.S.CtSat := by
  intro E _ _ _ n r φ ψ hφ hψ h0 w B hB
  let C : Submodule ℂ (Sm E n) :=
    { carrier := {f | Continuous f.1}
      add_mem' := fun h h' => Continuous.add h h'
      zero_mem' := continuous_const
      smul_mem' := fun c _ h => Continuous.const_smul h c }
  have hC : ∀ g, ∀ f ∈ C, fL n w g f ∈ C := fun g f hf =>
    show Continuous fun x => f.1 (x * finGL E n (locGL E n w g)) from
      Continuous.comp (show Continuous f.1 from hf) (continuous_id.mul continuous_const)
  have hc : φ ∈ C := ((UpperTheory.V.Cm.isAutForm_iff φ).1 hφ).continuous
  let F : C →ₗ[ℂ] (GA E n → ℂ) :=
    { toFun := fun f => constantTerm r f.1.1
      map_add' := fun f f' => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_add f.2 f'.2 g
      map_smul' := fun c f => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_smul c f.1.1 g }
  have h1 : IsSatVecGL w (GlobalTheory.PRep.sub (fL n w) C hC) ⟨φ, hc⟩ B :=
    IsSatVecGL.of_map C.subtype (fun _ _ => rfl) Subtype.val_injective hB
  have hF : F ⟨φ, hc⟩ = ψ.1 := hψ.symm
  have h2 := h1.map (ρ' := (GlobalTheory.PRep.rightReg ℂ (GA E n) ℂ).comp ((finGL E n).comp (locGL E n w))) F
    (fun g f => funext fun x =>
      GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate f.1.1 (finGL E n (locGL E n w g)) x)
    (by rw [hF]; exact fun h => h0 (Subtype.ext h))
  rw [hF] at h2
  exact IsSatVecGL.of_map (Sm E n).subtype (fun _ _ => rfl) Subtype.val_injective h2
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

open UpperTheory.V UpperTheory.V.Af.Fin in
private theorem lie_eq_lam {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (i j : Fin a) (x : Cinf E)
    (φ : Sm E a) :
    Cm.smEq E a (lie E a (toL (Matrix.single i j x)) φ) =
      lam E a (Matrix.single i j (Cm.mixEq E x)) (Cm.smEq E a φ) := by
  rw [← Cm.uAction_ι_smEq, lam_apply]
  congr 3
  refine Subtype.ext (Matrix.ext fun k l => ?_)
  change Cm.mixEq E (Matrix.single i j x k l) = Matrix.single i j (Cm.mixEq E x) k l
  simp only [Matrix.single_apply, apply_ite (Cm.mixEq E), map_zero]

open UpperTheory.V UpperTheory.V.Af.Fin in
theorem UpperTheory.V.Cj.S.slice :
    UpperTheory.V.Cj.S.Slice := by
  intro E _ _ _ a n e g
  obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie E a n e g
  have key : ∀ i j x ψ, (Cm.smEq E a).symm (f (Cm.smEq E n (lie E n (toL (Matrix.single (e i) (e j) x)) ψ))) =
      lie E a (toL (Matrix.single i j x)) ((Cm.smEq E a).symm (f (Cm.smEq E n ψ))) := fun i j x ψ => by
    rw [LinearEquiv.symm_apply_eq, lie_eq_lam, lie_eq_lam, LinearEquiv.apply_symm_apply, ← matrixExtendByZero_single, hl]
  refine ⟨(Cm.smEq E a).symm.toLinearMap ∘ₗ f ∘ₗ (Cm.smEq E n).toLinearMap, fun ψ x => hf _ x, fun t i j ψ => ?_⟩
  rw [← Cm.uC_genC, ← Cm.uC_genC]
  simp only [Cm.genC, AlgRepEndIrreducible.eL, map_smul, map_sub, Cm.uC_ιC, LinearMap.smul_apply, LinearMap.sub_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key]
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem slice_cap (h : UpperTheory.V.Cj.S.Slice) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n : ℕ}
    (e : Fin a ↪ Fin n) (g : GA E n) :
    ∃ f : Sm E n →ₗ[ℂ] Sm E a, (∀ ψ x, (f ψ).1 x = ψ.1 (g * emb e x)) ∧
      ∀ t u ψ, cap t u (f ψ) = f (capB e t u ψ) := by
  obtain ⟨f, hf, hE⟩ := h E a n e g
  exact ⟨f, hf, fun t u ψ => (UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ (hE t) _ ψ).symm⟩

theorem UpperTheory.V.Cj.S.capRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.CapBlock → UpperTheory.V.Cj.S.CapRel := by
  intro hS hB E _ _ _ r s ψ hψ t u
  refine ⟨res (capB (e1 r s) t (u - (s : ℂ) / 2) ψ).1, fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e1 r s) (emb (e2 r s) y)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = fun x => res φ.1 x y := fun φ => funext fun x => by
      rw [hf, res, blk, UpperTheory.V.Af.Fin.emb_comm]
    exact ⟨f ψ, key ψ, by rw [hc, key]⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e2 r s) (emb (e1 r s) x)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = res φ.1 x := fun φ => funext fun y => hf φ y
    refine ⟨f _, key _, ?_⟩
    rw [hc, key]
    exact funext fun y => (hB E r s ψ hψ t u x y).symm
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.step :
    UpperTheory.V.Cj.S.PairEig → UpperTheory.V.Cj.S.SliceBdd → UpperTheory.V.Cj.S.Iwa → UpperTheory.V.Cj.S.CtCap → UpperTheory.V.Cj.S.CtSat → UpperTheory.V.Cj.S.CapRel → UpperTheory.V.Cj.S.HkRel → UpperTheory.V.Cj.S.CapArith → UpperTheory.V.Cj.S.SatArith → UpperTheory.V.Cj.S.Step := by
  intro hPair hSlice hIwa hCtCap hCtSat hCapRel hHkRel hCapA hSatA E _ _ _ r s φ₀ m B h₀ hne₀
  obtain ⟨φ, hφ, hne⟩ := hIwa E r s φ₀ m B h₀ hne₀
  obtain ⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩ := hSlice E r s φ hφ.aut
  obtain ⟨ψ, hψ, hNI, hcap⟩ := hCtCap E (r + s) r φ hφ.aut
  rw [← hψ] at hne hs₁ hs₂
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, h⟩ := hne
    exact h rfl
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, hc, hs⟩ := hPair E r s (res ψ.1) S₁ S₂ hS₁ hS₂ hne hs₁ hs₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, fun t => ?_, fun ν ν' hν hν' => ?_⟩
  · refine hCapA (m t) (m₁ t) (m₂ t) _ _ fun u => ?_
    have e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2 := by push_cast; ring
    have e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine hc t _ _ _ _ (hCapRel E r s ψ hNI t u) fun x y => ?_
    rw [hcap t u, (hφ.cap t).2 u, hψ]
    simp only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact MeasureTheory.integral_const_mul _ _
  · filter_upwards [hφ.sat, h₁.sat, h₂.sat, hs] with w hw hw₁ hw₂ hw₃
    have hv := hCtSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) hw
    obtain ⟨ϖ, hu⟩ := exists_isUnifV w
    refine hSatA (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) hw.2.2.1 hw₁.2.2.1 hw₂.2.2.1 (fun j hj => ?_) _ _ ?_ ?_
    · obtain ⟨G, hG, hsum⟩ := hHkRel E r s ψ hNI w hv.2.1 ϖ hu j hj
      refine hw₃ ϖ hu _ G _ hG fun x y => ?_
      rw [hsum x y]
      have : tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ := hv.2.2.2 ϖ hu j hj
      rw [this]
      rfl
    · rw [hν.2.1 w]
      congr 1
      push_cast; ring
    · rw [hν'.2.1 w]
      congr 1
      push_cast; ring
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_map {ι α : Type} [Fintype ι] (f : α → α) (C : ι → Multiset α) :
    ∑ i, (C i).map f = (∑ i, C i).map f := by
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]

private theorem sat_twist {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CG E a) {w : Pl E}
    {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem UpperTheory.V.Cj.S.suppTwist :
    UpperTheory.V.Cj.S.SuppTwist := by
  rintro E _ _ _ a k m B ⟨ι, _, n, π, μ, hk, hn, ha, hμ, hm, hB⟩ x ν hν
  refine ⟨ι, inferInstance, n, fun i => (π i).twist ν, fun i t => (μ i t).map (· + (x : ℂ)), hk, hn, ha,
    fun i t => ?_, fun t => ?_, hB.mono ?_⟩
  · have h := (hμ i t).twist ν
    rwa [(InfType.expo_of_infType E ν).2.1 x hν t] at h
  · rw [sum_map, hm]
  · rintro w ⟨C, hC, hs⟩
    exact ⟨fun i => (C i).map (· * ν.val w), fun i => sat_twist _ (hC i) (hν.1 w), by rw [sum_map, hs]⟩
end

section
namespace UpperTheory.V.Cj.S

theorem suppAdd : SuppAdd := by
  intro E _ _ _ r s k l m₁ m₂ B₁ B₂ h₁ h₂
  obtain ⟨ι, _, n, π, μ, hk, hn, hs, hi, hm, hB⟩ := h₁
  obtain ⟨κ, _, n', π', μ', hk', hn', hs', hi', hm', hB'⟩ := h₂
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim n n', fun i => Sum.rec (fun i => π i) (fun i => π' i) i, Sum.elim μ μ',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
    exact Nat.add_le_add hk hk'
  · rintro (i | i)
    · exact hn i
    · exact hn' i
  · rw [Fintype.sum_sum_type, ← hs, ← hs']
    rfl
  · rintro (i | i) t
    · exact hi i t
    · exact hi' i t
  · intro t
    rw [Fintype.sum_sum_type]
    show ∑ i, μ i t + ∑ i, μ' i t = m₁ t + m₂ t
    rw [hm t, hm' t]
  · filter_upwards [hB, hB'] with w hw hw'
    obtain ⟨C, hC, hCs⟩ := hw
    obtain ⟨C', hC', hCs'⟩ := hw'
    refine ⟨Sum.elim C C', ?_, ?_⟩
    · rintro (i | i)
      · exact hC i
      · exact hC' i
    · rw [Fintype.sum_sum_type]
      show ∑ i, C i + ∑ i, C' i = B₁ w + B₂ w
      rw [hCs, hCs']

end UpperTheory.V.Cj.S
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun Formalism.L2.Host
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)

namespace UpperTheory.V.Cj.S

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem Supp.congr {a k : ℕ} {m m' : (E →+* ℂ) → Multiset ℂ} {B B' : Pl E → Multiset ℂˣ} (h : Supp E a k m B)
    (hm : ∀ t, m' t = m t) (hB : ∀ᶠ w in Filter.cofinite, B' w = B w) : Supp E a k m' B' := by
  obtain ⟨ι, _, n, π, μ, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ι, inferInstance, n, π, μ, h1, h2, h3, h4, fun t => (h5 t).trans (hm t).symm, ?_⟩
  filter_upwards [h6, hB] with w ⟨C, c1, c2⟩ e
  exact ⟨C, c1, c2.trans e.symm⟩

private theorem Supp.mono {a k l : ℕ} {m : (E →+* ℂ) → Multiset ℂ} {B : Pl E → Multiset ℂˣ} (h : Supp E a k m B)
    (hl : l ≤ k) : Supp E a l m B := by
  obtain ⟨ι, _, n, π, μ, h1, h2⟩ := h
  exact ⟨ι, inferInstance, n, π, μ, hl.trans h1, h2⟩

private theorem supp_two (hS : Step) (hT : SuppTwist) (hA : SuppAdd) {a : ℕ}
    (ih : ∀ b < a, 1 ≤ b → ∀ (φ : Sm E b) m B, Eig φ m B → Supp E b 1 m B)
    {φ : Sm E a} {m : (E →+* ℂ) → Multiset ℂ} {B : Pl E → Multiset ℂˣ} (h : Eig φ m B) (hc : ¬ IsCuspForm φ) :
    Supp E a 2 m B := by
  have h1 : ¬ GroundTheory.Automorphic.AutomorphicForm.IsCuspidal φ.1 := fun h2 =>
    hc ((Cm.isCuspForm_iff φ).2 ⟨(Cm.isAutForm_iff φ).1 h.aut, h2⟩)
  unfold GroundTheory.Automorphic.AutomorphicForm.IsCuspidal at h1
  push Not at h1
  obtain ⟨r, h0, hr, hg⟩ := h1
  obtain ⟨s, rfl⟩ : ∃ s, a = r + s := ⟨a - r, by omega⟩
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, e₁, e₂, hm, hB⟩ := hS E r s φ m B h hg
  have hν := fun x : ℝ => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) x
  exact (hA E r s 1 1 _ _ _ _ (hT E r 1 _ _ (ih r hr h0 _ _ _ e₁) _ _ (hν _))
    (hT E s 1 _ _ (ih s (by omega) (by omega) _ _ _ e₂) _ _ (hν _))).congr hm (hB _ _ (hν _) (hν _))

private theorem supp_one (hS : Step) (hT : SuppTwist) (hA : SuppAdd) (hC : SuppCusp) (a : ℕ) :
    1 ≤ a → ∀ (φ : Sm E a) m B, Eig φ m B → Supp E a 1 m B := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha φ m B h
    by_cases hc : IsCuspForm φ
    · exact hC E a ha φ m B h hc
    · exact (supp_two hS hT hA ih h hc).mono one_le_two

theorem cuspSupport_of (hS : Step) (hT : SuppTwist) (hA : SuppAdd) (hC : SuppCusp) (hP : CuspProj) (hτ : TauSat) :
    CuspSupport := by
  intro E _ _ _ a ha τ m j hj hfin haut hcap
  by_cases hc : ∀ v, IsCuspForm (j v)
  · left
    obtain ⟨v, hv⟩ : ∃ v, j v ≠ 0 := by
      by_contra h
      push Not at h
      exact hj (LinearMap.ext h)
    let j' : τ.V →ₗ[ℂ] CI a m := j.codRestrict _ fun v => mem_CI.2 ⟨hc v, fun t => (hcap v t).2⟩
    obtain ⟨π, h1, p, h2, h3⟩ := hP E a ha m (fun t => (hcap v t).1) (j' v) fun e => hv (congrArg Subtype.val e)
    exact ⟨π, ⟨p ∘ₗ j', fun e => h2 (LinearMap.congr_fun e v), fun g x => h3 g (j' x) (j' (τ.ρ g x)) (hfin g x)⟩, h1⟩
  · right
    push Not at hc
    obtain ⟨v, hv⟩ := hc
    have h0 : j v ≠ 0 := fun e => hv (e ▸ Cm.mem_range_ofCusp.1 (Submodule.zero_mem _))
    have hv0 : v ≠ 0 := fun e => h0 (by rw [e, map_zero])
    have h1 := hτ E a τ v hv0
    classical
    let B : Pl E → Multiset ℂˣ := fun w =>
      if h : ∃ B, HasSatGL w (locOf τ.ρ w) B ∧ IsSatVecGL w (locOf τ.ρ w) v B then h.choose else 0
    have h2 : ∀ᶠ w in Filter.cofinite, HasSatGL w (locOf τ.ρ w) (B w) ∧ IsSatVecGL w (locOf τ.ρ w) v (B w) :=
      h1.mono fun w h => by simp only [B, dif_pos h]; exact h.choose_spec
    have he : Eig (j v) m B :=
      ⟨h0, haut v, hcap v, h2.mono fun w h => h.2.map j (fun g y => hfin _ y) h0⟩
    obtain ⟨ι, _, n, π, μ, c1, c2, c3, c4, c5, c6⟩ :=
      supp_two hS hT hA (fun b _ => supp_one hS hT hA hC b) he hv
    refine ⟨ι, inferInstance, n, π, μ, c1, c2, fun i => ?_, c3, c4, c5, ?_⟩
    · obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card c1 i
      rw [← c3]
      exact Finset.single_lt_sum hk (Finset.mem_univ i) (Finset.mem_univ k) (c2 k) fun _ _ _ => Nat.zero_le _
    · filter_upwards [c6, h2] with w ⟨C, d1, d2⟩ h
      exact ⟨C, d1, d2 ▸ h.1⟩

theorem cuspSupport : CuspSupport :=
  cuspSupport_of
    (step (pairEig (twoVar tensEigB) (stabSp capAct levelSplit (hullBdd typesComm) (hullOps capAct)) (opComm capAct) satOfEig capOfEig) (sliceBdd singleBdd) (iwa (rtK capAct)) ctCap ctSat (capRel slice capBlock) (hkRel slice hkSum (hkLocal sumInner matBlock) gl2_local_to_adelic_embedding) capArith satArith)
    suppTwist suppAdd (suppCusp (cuspProj capAct (ciBasic capAct) (ciCompl (ciBasic capAct))))
    (cuspProj capAct (ciBasic capAct) (ciCompl (ciBasic capAct))) tauSat

end UpperTheory.V.Cj.S
end
end
