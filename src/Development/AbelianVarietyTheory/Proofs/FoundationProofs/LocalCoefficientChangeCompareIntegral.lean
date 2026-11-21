import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelmerLevel

section Comp

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {ι : Type} [Fintype ι]
  (b : Module.Basis ι O O')

structure Comp (A A' : Type) [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A'] where
  inc : A →+ A'
  p : ι → A' →+ A
  sum_p : ∀ x, ∑ a, b a • inc (p a x) = x
  p_inc : ∀ a c x, p a (c • inc x) = b.repr c a • x

def Comp.self : Comp b O O' where
  inc := (algebraMap O O').toAddMonoidHom
  p a := (b.coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm]
  p_inc a c x := by
    have : c • (algebraMap O O').toAddMonoidHom x = x • c := by simp [Algebra.smul_def, mul_comm]
    rw [this]; simp [mul_comm]

variable {b} {A A' : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A']

namespace Comp

variable (S : Comp b A A')

theorem ext_p {x y : A'} (h : ∀ a, S.p a x = S.p a y) : x = y := by
  rw [← S.sum_p x, ← S.sum_p y]; simp [h]

theorem p_inc' (a : ι) (x : A) : S.p a (S.inc x) = b.repr 1 a • x := by
  rw [← S.p_inc, one_smul]

theorem p_sum (m : ι → A) (a : ι) : S.p a (∑ a', b a' • S.inc (m a')) = m a := by
  classical
  simp [map_sum, S.p_inc, Finsupp.single_apply]

theorem inc_smul (o : O) (x : A) : S.inc (o • x) = algebraMap O O' o • S.inc x := by
  refine S.ext_p fun a => ?_
  rw [S.p_inc', S.p_inc, Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply,
    smul_eq_mul, smul_smul, mul_comm]

theorem p_smul (a : ι) (o : O) (x : A') : S.p a (algebraMap O O' o • x) = o • S.p a x := by
  classical
  conv_lhs => rw [← S.sum_p x]
  simp [Finset.smul_sum, smul_smul, S.p_inc, ← Algebra.smul_def, Finsupp.single_apply]

include S in
theorem length_eq : Module.length O' A' = Module.length O' (O' ⊗[O] A) := by
  letI : Module O A' := Module.compHom A' (algebraMap O O')
  haveI : IsScalarTower O O' A' := ⟨fun o c x => by
    change (o • c) • x = algebraMap O O' o • c • x
    rw [Algebra.smul_def, mul_smul]⟩
  let f : A →ₗ[O] A' := { S.inc with map_smul' := S.inc_smul }
  let F : O' ⊗[O] A →ₗ[O'] A' := f.liftBaseChange O'
  have hF : ∀ c x, F (c ⊗ₜ x) = c • S.inc x := fun c x => LinearMap.liftBaseChange_tmul _ _ _ _
  have hl : ∀ t, ∑ a, b a ⊗ₜ[O] S.p a (F t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      simp only [hF, S.p_inc, ← TensorProduct.smul_tmul]
      rw [← TensorProduct.sum_tmul, b.sum_repr]
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]
  refine (LinearEquiv.ofBijective F ⟨fun s t h => ?_, fun x => ⟨∑ a, b a ⊗ₜ[O] S.p a x, ?_⟩⟩).length_eq.symm
  · rw [← hl s, ← hl t, h]
  · simp only [map_sum, hF, S.sum_p]

def pi (X : Type) : Comp b (X → A) (X → A') where
  inc := AddMonoidHom.compLeft S.inc X
  p a := AddMonoidHom.compLeft (S.p a) X
  sum_p x := by funext g; simp [S.sum_p]
  p_inc a c x := by funext g; simp [S.p_inc]

def Compat (N : Submodule O A) (N' : Submodule O' A') : Prop := ∀ x, x ∈ N' ↔ ∀ a, S.p a x ∈ N

variable {S}

theorem Compat.inc_mem {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') {x : A}
    (hx : x ∈ N) : S.inc x ∈ N' :=
  (h _).2 fun a => by rw [S.p_inc']; exact N.smul_mem _ hx

def Compat.sub {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') : Comp b N N' where
  inc := { toFun x := ⟨S.inc x, h.inc_mem x.2⟩
           map_zero' := Subtype.ext (map_zero _)
           map_add' x y := Subtype.ext (map_add _ _ _) }
  p a := { toFun x := ⟨S.p a x, (h _).1 x.2 a⟩
           map_zero' := Subtype.ext (map_zero _)
           map_add' x y := Subtype.ext (map_add _ _ _) }
  sum_p x := Subtype.ext (by simpa using S.sum_p x)
  p_inc a c x := Subtype.ext (S.p_inc a c x)

def Compat.quot {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') :
    Comp b (A ⧸ N) (A' ⧸ N') where
  inc := QuotientAddGroup.map N.toAddSubgroup N'.toAddSubgroup S.inc fun _ hx => h.inc_mem hx
  p a := QuotientAddGroup.map N'.toAddSubgroup N.toAddSubgroup (S.p a) fun x hx => (h x).1 hx a
  sum_p x := by
    obtain ⟨x, rfl⟩ := N'.mkQ_surjective x
    conv_rhs => rw [← S.sum_p x, map_sum]
    rfl
  p_inc a c x := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    rw [← map_smul, ← S.p_inc]
    rfl

variable (S)




section Coh

variable [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
  [TopologicalSpace A'] [DiscreteTopology A'] [IsTopologicalAddGroup A'] [ContinuousConstSMul O' A']
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] {ρ : Representation O Γ A} {ρ' : Representation O' Γ A'}
  (he : ∀ a g m, S.p a (ρ' g m) = ρ g (S.p a m))
include he

theorem compatible_cocycles : (S.pi Γ).Compat (Z1 ρ) (Z1 ρ') := by
  intro f
  constructor
  · intro hf a
    refine ⟨(continuous_of_discreteTopology (f := S.p a)).comp hf.1, fun g h => ?_⟩
    change S.p a (f (g * h)) = S.p a (f g) + ρ g (S.p a (f h))
    rw [hf.2, map_add, he]
  · intro hf
    refine ⟨?_, fun g h => S.ext_p fun a => ?_⟩
    · have : f = fun g => ∑ a, b a • S.inc (S.p a (f g)) := by funext g; rw [S.sum_p]
      rw [this]
      exact continuous_finset_sum _ fun a _ =>
        ((continuous_of_discreteTopology (f := S.inc)).comp (hf a).1).const_smul (b a)
    · rw [map_add, he]; exact (hf a).2 g h

theorem compatible_coboundaries : (S.compatible_cocycles he).sub.Compat ((B1 ρ).comap (Z1 ρ).subtype)
    ((B1 ρ').comap (Z1 ρ').subtype) := by
  intro f
  simp only [Submodule.mem_comap, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ a
    refine ⟨S.p a m, fun g => ?_⟩
    change S.p a (f.1 g) = _
    rw [← he, ← map_sub]; exact congrArg _ (hm g)
  · intro hf
    choose m hm using hf
    refine ⟨∑ a', b a' • S.inc (m a'), fun g => S.ext_p fun a => ?_⟩
    rw [map_sub, he, S.p_sum]
    exact hm a g

def h1 : Comp b (H1 ρ) (H1 ρ') := (S.compatible_coboundaries he).quot

theorem p_res {Δ : Type} [Group Δ] [TopologicalSpace Δ] (φ : Δ →* Γ) (hφ : Continuous φ) (a : ι)
    (x : H1 ρ') :
    (S.h1 (ρ := ρ.comp φ) (ρ' := ρ'.comp φ) (fun a g m => he a (φ g) m)).p a (resH1 ρ' φ hφ x) =
      resH1 ρ φ hφ ((S.h1 he).p a x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl



end Coh

end Comp

end Comp

section Frac

variable {O O' : Type} [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O'] [Algebra O O']
  [FaithfulSMul O O'] [Module.Finite O O'] {ι : Type} [Fintype ι] (b : Module.Basis ι O O')

attribute [local instance] FractionRing.liftAlgebra

def fracBasis : Module.Basis ι (FractionRing O) (FractionRing O') :=
  b.localizationLocalization (FractionRing O) (nonZeroDivisors O) (FractionRing O')

def fracComp : Comp b (FractionRing O) (FractionRing O') where
  inc := (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom
  p a := ((fracBasis b).coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← (fracBasis b).sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm, fracBasis]
  p_inc a c x := by
    have : c • (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom x =
        x • algebraMap O' (FractionRing O') c := by simp [Algebra.smul_def, mul_comm]
    rw [this]
    change (fracBasis b).repr (x • _) a = _
    rw [map_smul, Finsupp.smul_apply, fracBasis, Module.Basis.localizationLocalization_repr_algebraMap,
      Algebra.smul_def (b.repr c a), smul_eq_mul, mul_comm]

theorem fracComp_inc (x : FractionRing O) :
    (fracComp b).inc x = algebraMap (FractionRing O) (FractionRing O') x := rfl

theorem frac_compat : (fracComp b).Compat (LinearMap.range (Algebra.linearMap O (FractionRing O)))
    (LinearMap.range (Algebra.linearMap O' (FractionRing O'))) := by
  intro x
  constructor
  · rintro ⟨c, rfl⟩ a
    refine ⟨b.repr c a, ?_⟩
    have := (fracComp b).p_inc a c 1
    simpa [fracComp_inc, ← Algebra.algebraMap_eq_smul_one] using this.symm
  · intro h
    choose m hm using h
    rw [← (fracComp b).sum_p x]
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ⟨algebraMap O O' (m a), ?_⟩
    rw [← hm, fracComp_inc]
    simp [← IsScalarTower.algebraMap_apply]

def divComp (r : ℕ) : Comp b (Fin r → KmodO O) (Fin r → KmodO O') := (frac_compat b).quot.pi (Fin r)


open Formalism.MainNotions.BlochKatoReduction


def fracClasses {Γ O₀ : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O₀] {O : Type} [CommRing O]
    [IsDomain O] (φ : O₀ →+* O) {r : ℕ} (ρ : Representation O Γ (Fin r → KmodO O)) {C : Type}
    (P : C → Prop) (Fr : C → Γ → Fin r → O₀ → O₀ → Prop) : Set (H1 ρ) :=
  {x | ∃ (z : Z1 ρ) (c : C) (y : Γ → Fin r → FractionRing O), P c ∧
    (∀ g a, ∃ n d : O₀, Fr c g a n d ∧
      algebraMap O (FractionRing O) (φ d) * y g a = algebraMap O (FractionRing O) (φ n)) ∧
    (∀ g a, (z : Γ → Fin r → KmodO O) g a = Submodule.Quotient.mk (y g a)) ∧
    x = Submodule.Quotient.mk z}


end Frac

section Len

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] [FaithfulSMul O O'] [Module.Finite O O']
  {ι : Type} [Fintype ι] {b : Module.Basis ι O O'}



end Len

section Main

open Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.GaloisCohomology


variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

open Classical in

def bkG {O : Type} [CommRing O] [IsDomain O] (φ : X.O0 i →+* O) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule O (H1 ((twRep φ (X.rhoS i s) (chiS i s) 1).comp (DecV N v).subtype)) :=
  if hv : v ∈ placesOver D.host.E (X.l i) then
    Submodule.span O (fracClasses φ _
      (fun c => c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)))
      (fun c g a n d => IsFrac bkP i v hv (c ((bkP.br i v hv).e g) a) n d))
  else ⊥

def selG {O : Type} [CommRing O] [IsDomain O] (φ : X.O0 i →+* O)
    (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    Submodule O (H1 (twRep φ (X.rhoS i s) (chiS i s) 1)) :=
  SelAll _ N.plOm (bkCond _ N.plOm (X.l i) (Spl i ∪ ↑Q) (bkG bkP i s φ))




end Main


end GlobalTheory.SelmerLevel

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.BlochKatoBaseChange

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem mem_HfD_iff (L : Lattice (O := O) ρ) (c : G → V ⧸ L.T) :
    c ∈ HfD PD L ↔ ∃ z ∈ finiteCocycles PD ρ, ∃ v : V, ∀ g, c g = Submodule.Quotient.mk (z g + (ρ g v - v)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz1, rfl⟩, _, ⟨v, rfl⟩, h⟩ := Submodule.mem_sup.1 hc
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨z, hz1, v, fun g => (congrFun h g).symm⟩
  · rintro ⟨z, hz, v, h⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk v, rfl⟩, funext fun g => (h g).symm⟩

end Gen

section Coord

variable {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [CommRing O] [IsDomain O]
  {f : O₀ →+* O} {hf : Function.Injective f} (p : FractionRing O →+ FractionRing O₀)
  (hp : ∀ y x, p (fracMap f hf y * x) = y * p x)
  (hi : ∀ c : O, ∃ d : O₀, p (algebraMap O _ c) = algebraMap O₀ _ d)

def coordQ (k : ℕ) : KOG O k →+ KOG O₀ k :=
  QuotientAddGroup.map (stdG O (FractionRing O) k).toAddSubgroup (stdG O₀ (FractionRing O₀) k).toAddSubgroup
    (AddMonoidHom.compLeft p (Fin k)) (by
      rintro _ ⟨u, rfl⟩
      choose d hd using hi
      exact ⟨fun j => d (u j), funext fun j => (hd (u j)).symm⟩)

theorem coordQ_mk {k : ℕ} (x : Fin k → FractionRing O) :
    coordQ p hi k (Submodule.Quotient.mk x) = Submodule.Quotient.mk (fun j => p (x j)) := rfl

include hp in
theorem coordQ_act {Γ : Type} [Group Γ] {k : ℕ} (M₀ : Γ →* Matrix (Fin k) (Fin k) O₀) (g : Γ) (x : KOG O k) :
    coordQ p hi k (WKG (mapM f M₀) g x) = WKG M₀ g (coordQ p hi k x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change coordQ p hi k (Submodule.Quotient.mk
      ((((M₀ g).map f).map (algebraMap O (FractionRing O))).mulVec x)) =
    Submodule.Quotient.mk (((M₀ g).map (algebraMap O₀ (FractionRing O₀))).mulVec fun j => p (x j))
  rw [coordQ_mk]
  congr 1
  funext j
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, ← fracMap_alg f hf, hp]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  [Algebra ℤ_[l] O₀] [TopologicalSpace O₀] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O)

include hp in
theorem exists_coordLL (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1, ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x) := by
  obtain ⟨φ, hφ⟩ := exists_coefMap B₀ B f hf hz
  let e := RingEquiv.ofBijective _ (toLLK_bijective B)
  let q : ↥B.LL.1 →+ ↥B₀.LL.1 := (Br.toLLK B₀).toAddMonoidHom.comp (p.comp e.symm.toAddMonoidHom)
  have hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x) := fun x =>
    congrArg (fun y => Br.toLLK B₀ (p y)) (e.symm_apply_apply x)
  refine ⟨{ q with map_smul' := fun r x => ?_ }, hq⟩
  obtain ⟨x, rfl⟩ := (toLLK_bijective B).2 x
  obtain ⟨y, hy⟩ := (toLLK_bijective B₀).2 (algebraMap ℚ_[l] _ r)
  change q (r • Br.toLLK B x) = r • q (Br.toLLK B x)
  rw [Algebra.smul_def, Algebra.smul_def, ← φ.commutes, ← hy, hφ, ← map_mul, hq, hq, hp, map_mul]

set_option synthInstance.maxHeartbeats 400000 in
theorem phi_coordQ {k : ℕ} (q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1)
    (hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x)) (x : KOG O k) (w : Fin k → Br.LLw B)
    (h : Br.phi B k x = Submodule.Quotient.mk w) :
    Br.phi B₀ k (coordQ p hi k x) = Submodule.Quotient.mk (fun j => q (w j)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : (Submodule.Quotient.mk (fun j => Br.toLLK B (x j)) :
      (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) = Submodule.Quotient.mk w := h
  change (Submodule.Quotient.mk (fun j => Br.toLLK B₀ (p (x j))) :
      (Fin k → Br.LLw B₀) ⧸ stdG (Br.Ow B₀) (Br.LLw B₀) k) = _
  rw [Submodule.Quotient.eq] at h1 ⊢
  obtain ⟨u, hu⟩ := h1
  choose d hd using id hi
  refine ⟨fun j => B₀.eO (d (B.eO.symm (u j))), funext fun j => ?_⟩
  have h2 : algebraMap (Br.Ow B) (Br.LLw B) (u j) = Br.toLLK B (x j) - w j := congrFun hu j
  change algebraMap (Br.Ow B₀) (Br.LLw B₀) _ = Br.toLLK B₀ (p (x j)) - q (w j)
  rw [← Br.toLLK_alg, ← hd, ← hq, ← hq, ← map_sub, ← h2, Br.toLLK_alg, RingEquiv.apply_symm_apply]

include hp in
theorem coordLL_mulVec {k : ℕ} (q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1)
    (hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x)) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀)
    (g : ↥(GK B₀.Kw)) (v : Fin k → Br.LLw B) :
    (fun j => q ((Br.locM B (mapM f M₀) (B.e (B₀.e.symm g))).mulVec v j)) =
      (Br.locM B₀ M₀ g).mulVec fun j => q (v j) := by
  choose x hx using fun j => (toLLK_bijective B).2 (v j)
  funext j
  have h1 : ∀ i, Br.locM B (mapM f M₀) (B.e (B₀.e.symm g)) j i =
      Br.toLLK B (fracMap f hf (algebraMap O₀ _ (M₀ (B₀.e.symm g) j i))) := by
    intro i
    rw [fracMap_alg, Br.toLLK_alg]
    change algebraMap (Br.Ow B) (Br.LLw B) (B.eO (f (M₀ (B.e.symm (B.e (B₀.e.symm g))) j i))) = _
    rw [MulEquiv.symm_apply_apply]
  have h2 : ∀ i, Br.locM B₀ M₀ g j i = Br.toLLK B₀ (algebraMap O₀ _ (M₀ (B₀.e.symm g) j i)) := by
    intro i
    rw [Br.toLLK_alg]
    rfl
  simp only [Matrix.mulVec, dotProduct, map_sum, h1, h2, ← hx, ← map_mul, hq, hp]

include hp in
set_option synthInstance.maxHeartbeats 400000 in
theorem coordQ_mem_HfD (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z)
    (P : LocPrime l) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    {k : ℕ} (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (c : ↥Gw → KOG O k)
    (hc : (fun g => Br.phi B k (c (Br.ι B g))) ∈ HfD (P.PD B.Kw) (Br.lat B (mapM f M₀))) :
    (fun g => Br.phi B₀ k (coordQ p hi k (c (Br.ι B₀ g)))) ∈ HfD (P.PD B₀.Kw) (Br.lat B₀ M₀) := by
  obtain ⟨q, hq⟩ := exists_coordLL p hp B₀ B hz
  obtain ⟨z, hz1, v, h⟩ := (mem_HfD_iff _ _ _).1 hc
  let θ : ↥(GK B₀.Kw) →* ↥(GK B.Kw) := B.e.toMonoidHom.comp B₀.e.symm.toMonoidHom
  have hθ : Continuous θ := B.e_cont.comp B₀.e_symm_cont
  have hσ' : ∀ g : ↥(GK B₀.Kw), (g : GQ l) = σ⁻¹ * (θ g : GQ l) * σ⁻¹⁻¹ := by
    intro g
    change _ = σ⁻¹ * (B.e (B₀.e.symm g) : GQ l) * σ⁻¹⁻¹
    rw [hσ, MulEquiv.apply_symm_apply]
    group
  have hm := coordLL_mulVec p hp B₀ B q hq M₀
  have hz2 := crystallineCocycle_transport_conjugation P B.Kw B₀.Kw B.LL B₀.LL θ hθ σ⁻¹ hσ' (Br.locM B (mapM f M₀)) (Br.locM B₀ M₀) q hm z hz1
  refine (mem_HfD_iff _ _ _).2 ⟨_, hz2, fun j => q (v j), fun g => ?_⟩
  have h3 : Br.phi B k (c (Br.ι B₀ g)) = Submodule.Quotient.mk
      (z (θ g) + ((Br.locM B (mapM f M₀) (θ g)).mulVec v - v)) := by
    have h4 : Br.ι B (θ g) = Br.ι B₀ g := B.e.symm_apply_apply _
    rw [← h4]
    exact h (θ g)
  refine (phi_coordQ p hi B₀ B q hq _ _ h3).trans ?_
  change _ = (Submodule.Quotient.mk ((fun j => q (z (θ g) j)) +
    ((Br.locM B₀ M₀ g).mulVec (fun j => q (v j)) - fun j => q (v j))) :
      (Fin k → Br.LLw B₀) ⧸ stdG (Br.Ow B₀) (Br.LLw B₀) k)
  rw [← hm]
  congr 1
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub]
  rfl

end Coord

theorem exists_coords {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [CommRing O]
    [IsDomain O] (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O₀] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → O) (p : ι → FractionRing O →+ FractionRing O₀),
      (∀ a y x, p a (fracMap f hf y * x) = y * p a x) ∧
      (∀ a (c : O), ∃ d : O₀, p a (algebraMap O _ c) = algebraMap O₀ _ d) ∧
      ∀ x, ∑ a, b a • fracMap f hf (p a x) = x := by
  letI := f.toAlgebra
  haveI : IsScalarTower ℤ_[l] O₀ O := IsScalarTower.of_algebraMap_eq fun z => (hz z).symm
  haveI : Module.Finite O₀ O := Module.Finite.of_restrictScalars_finite ℤ_[l] O₀ O
  haveI : FaithfulSMul O₀ O := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  letI := FractionRing.liftAlgebra O₀ (FractionRing O)
  let b := Module.Free.chooseBasis O₀ O
  have he : ∀ y, fracMap f hf y = algebraMap (FractionRing O₀) (FractionRing O) y := by
    intro y
    refine DFunLike.congr_fun (IsFractionRing.ringHom_ext (A := O₀) fun z => ?_ :
      fracMap f hf = algebraMap (FractionRing O₀) (FractionRing O)) y
    rw [fracMap_alg, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O₀ O (FractionRing O)]
    rfl
  refine ⟨_, inferInstance, b, (SelmerLevel.fracComp b).p, fun a y x => ?_, fun a c => ?_, fun x => ?_⟩
  · rw [he, ← Algebra.smul_def]
    exact ((SelmerLevel.fracBasis b).coord a).map_smul y x
  · obtain ⟨d, hd⟩ := (SelmerLevel.frac_compat b _).1 ⟨c, rfl⟩ a
    exact ⟨d, hd.symm⟩
  · simp only [he]
    exact (SelmerLevel.fracComp b).sum_p x

set_option synthInstance.maxHeartbeats 400000 in

theorem bkG_le_extCond (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O₀ O : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [Algebra ℤ_[l] O₀] [Module.Finite ℤ_[l] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O]
    (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z)
    (k : ℕ) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) :
    Br.bkG B P (WKG (mapM f M₀)) (mapM f M₀) ≤
      extCond f hf (WKG M₀) (Br.bkG B₀ P (WKG M₀) M₀) (WKG (mapM f M₀)) := by
  obtain ⟨ι, _, b, p, hp, hi, hs⟩ := exists_coords l f hf hz
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, ?_, rfl⟩
  have hsum : (c : ↥Gw → KOG O k) =
      ∑ a, b a • fun g => pushKO f hf k (coordQ (p a) (hi a) k ((c : ↥Gw → KOG O k) g)) := by
    funext g
    rw [Finset.sum_apply]
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ ((c : ↥Gw → KOG O k) g)
    have : x = ∑ a, b a • fun j => fracMap f hf (p a (x j)) := by
      funext j
      rw [Finset.sum_apply]
      exact (hs (x j)).symm
    simp only [Pi.smul_apply, ← hx]
    conv_lhs => rw [this, map_sum]
    rfl
  change (c : ↥Gw → KOG O k) ∈ Submodule.span O _
  rw [hsum]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have hZ : (fun g => coordQ (p a) (hi a) k ((c : ↥Gw → KOG O k) g)) ∈ Z1 (WKG M₀) :=
    ⟨(continuous_of_discreteTopology (f := coordQ (p a) (hi a) k)).comp c.2.1, fun g h => by
      beta_reduce
      rw [c.2.2, map_add, coordQ_act (p a) (hp a)]⟩
  exact ⟨⟨_, hZ⟩, ⟨⟨_, hZ⟩, coordQ_mem_HfD (p a) (hp a) (hi a) B₀ B hz P σ hσ M₀ c hc, rfl⟩, rfl⟩

end GlobalTheory.BlochKatoBaseChange

end
end
