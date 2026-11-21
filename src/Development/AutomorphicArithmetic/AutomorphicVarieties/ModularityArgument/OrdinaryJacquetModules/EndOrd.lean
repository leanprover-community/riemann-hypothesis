import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.FiniteOverL
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.BnRepLin

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}






private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩

private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl

private theorem push_comp {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (χ : Γ →* Aˣ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : W.pushCh y (W.pushCh f χ) = W.pushCh x χ := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl

end SlopeTestRemainingChoices

set_option maxHeartbeats 1000000 in
private theorem absPt (hC : CoreOrd) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
    (hθ : H.IsWt θ) (ι : Qbar l ≃+* ℂ) {P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.Part ι lam ξ → Prop}
    (hP : AutY H ι P) (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)]
    {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)
    (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a K) (hm : H.IsMap θ a K D₀ ψ₀ f) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n)
    (hl : lam ∈ H.admitted) (har : H.Arith θ (x.comp j).toRingHom lam) :
    ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.Part ι lam ξ), P lam d ξ Y ∧ D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat Y.r) ∧
      ∀ v, ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, IsSubquotient (Y.σl v).ρ (PS ω) ∧
        ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh (x : R →+* Qbar l) (ψ₀ v i)) := by
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  have har' : H.Arith θ (y.toRingHom.comp (algebraMap A _)) lam := by rw [e1]; exact har
  unfold HSet.IsMap at hm
  obtain ⟨d, ξ, Y, hY, hD, hω⟩ := hC L Ω l n c H hA A θ hθ ι P hP a K _ _ hm lam hl y har'
  refine ⟨d, ξ, Y, hY, (map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD, fun v => ?_⟩
  obtain ⟨ω, h1, h2⟩ := hω v
  refine ⟨ω, h1, fun i => ?_⟩
  have := h2 i
  rwa [push_comp _ f.toRingHom y.toRingHom x hy] at this

set_option maxHeartbeats 1000000 in
private theorem core (H : Af.HypothesesH) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V} {c : Coef l}
    {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : HD Q ι Λ} {K : (hset Q R.τ₀).Lev}
    {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ (lam : Wt L l n) (d : ℕ) (ξ : GV n (hset Q R.τ₀).Sl →* GL (Fin d) ℂ) (Y : (hset Q R.τ₀).Part ι lam ξ),
      (Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧
        Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q R.τ₀).Sl v) (Y.σl v)) ∧
      x.IsRep (Y.r.comp V.pr) ∧
      ∀ v : Vl l L, ∃ ω : Fin n → (((hset Q R.τ₀).Sl v).adicCompletion L)ˣ →* ℂˣ, IsSubquotient (Y.σl v).ρ (PS ω) ∧
        ∀ i, OrdChar ι ((hset Q R.τ₀).art v) (ω i) (htW lam i) (x.psi v i) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := wtBridge H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  obtain ⟨d, ξ, Y, hY, hD, hω⟩ := absPt (coreOrd H.litN) (hset Q R.τ₀) (axU H.litN l L Ω s n hn V Q c R.m R.τ₀) R.θ R.isWt ι
    (autUO H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) R.a K B.u.D B.u.ψ (Λ.toPair B.u) f hmap hsurj hlam x hx lam (Set.mem_univ _) har
  refine ⟨lam, d, ξ, Y, hY, ?_, hω⟩
  replace hD : x.D = W.GDet.ofRep (W.mat Y.r) := hD
  change x.D.comap V.pr = _
  rw [hD]
  exact (AlgebraTools.Det.repApi (W.mat Y.r)).2.2.2.2.2.2.1 V.pr
