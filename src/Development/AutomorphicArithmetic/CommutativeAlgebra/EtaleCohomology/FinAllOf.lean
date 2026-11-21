import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Final
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiHIterSmul
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiAZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TorsionOfVec
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NatCastQb
import Development.AutomorphicArithmetic.EtaleIdempotents.GaloisEquivariantTensorDescentOfPrimePowerUnits
import Development.AutomorphicArithmetic.EtaleIdempotents.IntegersResidueEqZeroOfNotIsUnit
import Development.AutomorphicArithmetic.EtaleIdempotents.CrisFrobeniusIterateEvalEtaleFamily
import Development.AutomorphicArithmetic.EtaleIdempotents.GaloisActionEvalEtaleFamilyExistsDenominator
import Development.AutomorphicArithmetic.EtaleIdempotents.EvalEtaleFamilyMemLimitOfReduced
import Development.AutomorphicArithmetic.EtaleIdempotents.IntegersResidueEqThetaCoeffPowOfTeichmuller
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.EtaleMapFirstChern
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
import GroundTheory.PAdicHodge.UnramifiedFrob
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernUnique
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAffFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ResidueExistence.ResEx

section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private theorem gRes_pow (r : Res l K) (f : ℕ) (hk : ∀ x : r.k, x ^ l ^ f = x) (x : OK l K) : gRes r x ^ l ^ f = gRes r x := by
  change (Ideal.Quotient.mk _) (r.s (r.ρ x)) ^ l ^ f = (Ideal.Quotient.mk _) (r.s (r.ρ x))
  rw [← map_pow, ← map_pow, hk]

private theorem galA_tA (g : K.fixingSubgroup) : ∃ χ : ℤ_[l]ˣ, galA g (tA l) = zA l χ * tA l :=
  ⟨cycloChar K (IntermediateField.fixingSubgroupEquiv K g), by
    have := ACris.gal_smul_periodT (K := K) (IntermediateField.fixingSubgroupEquiv K g) (untilt_epsilon (p := l))
    rwa [ACris.gal_smul_def] at this⟩

private theorem phiA_tA : phiA l (tA l) = (l : Acris l) * tA l := ACris.phi_periodT_eq_mul _

private theorem phiA_zA (x : ℤ_[l]) : phiA l (zA l x) = zA l x := by
  change ACris.phi ℂ_[l] l (algebraMap (Ainf l) (Acris l) (IsPerfectoidField.padicIntToWitt l x)) = _
  rw [ACris.phi_algebraMap, ACris.frobenius_padicIntToWitt]
  rfl

private theorem aux_sub {R Mo : Type*} [CommRing R] [AddCommGroup Mo] [Module R Mo] (A X t : R) (u s : ℕ) (G E : Mo)
    (h : A • G = (A * X ^ s) • E) : A • ((X * t) ^ u • G) - (A * X ^ (u + s)) • (t ^ u • E) = 0 := by
  rw [smul_comm A, h, smul_smul, smul_smul, ← sub_smul]
  convert zero_smul R E using 2
  ring

private theorem iter_smul_gen {R Mo : Type*} [SMul R Mo] (φ : R → R) (ϕ : Mo → Mo)
    (h : ∀ (a : R) (x : Mo), ϕ (a • x) = φ a • ϕ x) (N : ℕ) (a : R) (x : Mo) :
    ϕ^[N] (a • x) = (φ^[N] a) • ϕ^[N] x := by
  induction N generalizing a x with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, h, ih, Function.iterate_succ_apply, Function.iterate_succ_apply]

private theorem phi_iter_smul (P : PAlg l ⥤ Type) (n j N : ℕ) (a : Acris l) (x : MH P n j) :
    (phiH P n j)^[N] (a • x) = ((phiA l)^[N] a) • (phiH P n j)^[N] x :=
  iter_smul_gen (phiA l) (phiH P n j) (fun a x => LinearMap.map_smulₛₗ ((phiMor P n).pull j) a x) N a x

private theorem phiA_iter_l (N : ℕ) : (phiA l)^[N] (l : Acris l) = l := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', ih, map_natCast]

private theorem phiA_iterate_tA (N : ℕ) : (phiA l)^[N] (tA l) = (l : Acris l) ^ N * tA l := by
  induction N with
  | zero => simp
  | succ N ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, phiA_tA]; ring

private theorem phiA_iterate_zA (N : ℕ) (x : ℤ_[l]) : (phiA l)^[N] (zA l x) = zA l x := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', ih, phiA_zA]

private theorem chain1 {R Q H Γ : Type*} {Mn : ℕ → Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup H] [Module R H]
    [∀ n, AddCommGroup (Mn n)] [∀ n, Module R (Mn n)] (l : ℕ) (t : R) (φ : R →+* R) (σ : Γ → R →+* R) (X : Γ → R)
    (b : ∀ n, H →ₗ[R] Mn n) (G : Γ → H → H) (γ : ∀ g n, Mn n →ₛₗ[σ g] Mn n) (u s N : ℕ) (α : H →+ Q) (T : Γ → Q →+ Q)
    (hker : ∀ x, (∀ n, b n x = 0) → t ^ u • x = 0) (hgal : ∀ g x n, b n (G g x) = γ g n (b n x))
    (E : ∀ n, Mn n) (h : H) (hh : ∀ n, b n h = t ^ u • E n) (hχ : ∀ g, σ g t = X g * t)
    (hl : φ^[N] (l : R) = l) (ht : φ^[N] t = (l : R) ^ N * t) (hX : ∀ g, φ^[N] (X g) = X g)
    (lin : ∀ (a : R) x, α (a • x) = (φ^[N] a) • α x) (gal : ∀ g x, α (G g x) = T g (α x))
    (hab : ∀ g, ∃ a b' : ℕ, ∀ n, ((l : R) ^ a * t ^ b') • γ g n (E n) = ((l : R) ^ a * t ^ b' * X g ^ s) • E n) (g : Γ) :
    ∃ a b' : ℕ, ((l : R) ^ a * t ^ b') • T g (α h) = ((l : R) ^ a * t ^ b' * X g ^ (u + s)) • α h := by
  obtain ⟨a, c, hac⟩ := hab g
  have h0 := hker (((l : R) ^ a * t ^ c) • G g h - ((l : R) ^ a * t ^ c * X g ^ (u + s)) • h) fun n => by
    rw [map_sub, map_smul, map_smul, hgal, hh]
    have e2 : γ g n (t ^ u • E n) = (X g * t) ^ u • γ g n (E n) := by
      rw [← hχ g, LinearMap.map_smulₛₗ, map_pow]
    rw [e2]
    exact aux_sub _ _ _ _ _ _ _ (hac n)
  rw [smul_sub, smul_smul, smul_smul, sub_eq_zero] at h0
  have h1 := congrArg α h0
  rw [lin, lin, gal] at h1
  have it : ∀ (x y : R), φ^[N] (x * y) = φ^[N] x * φ^[N] y := fun x y => iterate_map_mul φ N x y
  have ip : ∀ (x : R) (k : ℕ), φ^[N] (x ^ k) = (φ^[N] x) ^ k := fun x k => iterate_map_pow φ N x k
  simp only [it, ip, hl, ht, hX] at h1
  refine ⟨a + N * (c + u), c + u, ?_⟩
  convert h1 using 2 <;> ring

private theorem chain2 {R Q H : Type*} {Mn : ℕ → Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup H] [Module R H]
    [∀ n, AddCommGroup (Mn n)] [∀ n, Module R (Mn n)] (l : ℕ) (t : R) (φ : R →+* R)
    (b : ∀ n, H →ₗ[R] Mn n) (P : H → H) (ϕ : ∀ n, Mn n → Mn n) (u r N e a' b' : ℕ) (α : H → Q) (β : Q →ₗ[R] H) (h : H) (q : Q)
    (E E' : ∀ n, Mn n) (hh : ∀ n, b n h = t ^ u • E n) (hl : φ^[N] (l : R) = l) (ht : φ^[N] t = (l : R) ^ N * t)
    (hy : ((l : R) ^ a' * t ^ b') • α h = t ^ (b' + (u + r)) • q) (fac : β (α h) = (l : R) ^ e • P^[N] h)
    (hphi : ∀ x n, b n (P x) = ϕ n (b n x)) (hit : ∀ n (a : R) x, (ϕ n)^[N] (a • x) = (φ^[N] a) • (ϕ n)^[N] x)
    (hE : ∀ n, (ϕ n)^[N] (E n) = E' n) (n : ℕ) :
    ((l : R) ^ (a' + e + N * u) * t ^ (b' + u)) • E' n = t ^ (b' + u + r) • b n (β q) := by
  have hP : ∀ (k : ℕ) x, b n (P^[k] x) = (ϕ n)^[k] (b n x) := fun k => by
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hphi, ih]
  have h1 := congrArg (fun x => b n (β x)) hy
  simp only [map_smul, fac, smul_smul, hP, hh, hit, hE] at h1
  have ip : ∀ (x : R) (k : ℕ), φ^[N] (x ^ k) = (φ^[N] x) ^ k := fun x k => iterate_map_pow φ N x k
  simp only [ip, ht, smul_smul] at h1
  have e1 : t ^ (b' + u + r) = t ^ (b' + (u + r)) := by rw [add_assoc]
  rw [e1, ← h1]
  congr 1
  ring

private theorem keyStep {r : Res l K} {M : Model l K} {f N j : ℕ} (hk : ∀ x : r.k, x ^ l ^ f = x)
    {Fr : PQ M.p (gRes r) ⟶ PQ M.p (gRes r)} {ρ : M.P ⟶ PQ M.p (gRes r)} (hFr : IsFr f Fr) (hρ : IsRd N ρ)
    (F : Pb.Fac r N) (hPin : Pin F M j) (y : Pb.LW r M j) (n : ℕ) :
    ∃ x : MH (PQ M.p (gRes r)) n j, (phiH _ n j)^[f] x = pullH Fr n j x ∧
      betaM M n j (levH (F.β M j ((1 : Pb.AW r) ⊗ₜ y)) n) = pullH ρ n j x :=
  Exists.elim (hPin n) fun m hm =>
    Exists.elim (absCl l K r M f N n j hk Fr ρ hFr hρ m hm.1 (y.1 n)) fun x hx =>
      ⟨x, hx.1, (congrArg (betaM M n j) (hm.2 y)).trans hx.2⟩

private def bl (M : Model l K) (j n : ℕ) : (M.HS true j).lim →ₗ[Acris l] M.MH n j :=
  (B.β (B.schFn M.p) (okToOC l K) true n j).comp ((LinearMap.proj n).comp (M.HS true j).lim.subtype)

private theorem witt_fac (k : Type) [Field k] [CharP k l] [PerfectRing k l] (y : WittVector l k) (hy : y ≠ 0) :
    ∃ (m : ℕ) (b : WittVector l k), y = (l : WittVector l k) ^ m * b ∧ IsUnit b := by
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' y hy
  exact ⟨m, b, e, b.isUnit⟩

private theorem isUnit_l (B₀ : PB l K) : IsUnit (l : B₀.C) := by
  have h : (l : B₀.C) = algebraMap ℚ_[l] B₀.C (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)).map _

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.absInvOf :
    UpperTheory.Ru.crystallineComparison.AbsInvOf := by
  intro l _ K r B₀ hC e he M hM f N j hk hfN hT F hPin hB ϖ hϖ
  obtain ⟨N', rfl⟩ := hfN
  have hg := gRes_pow r f hk
  obtain ⟨⟨Fr, hFr⟩, hρ', -⟩ := frEx l (OK l K) M.X M.p (okToOC l K) (gRes r) (f * N') f hg
  obtain ⟨ρ, hρ⟩ := hρ' (fun x w h => UpperTheory.integersResidue_eq_theta_coeff_pow_of_teichmuller r _ hT x w h)
  refine ⟨f * N', N', gRes r, Fr, ρ, UpperTheory.integersResidue_eq_zero_of_not_isUnit r ϖ hϖ, hg, hFr, hρ, ?_⟩
  intro ι _ v c s hinv
  obtain ⟨⟨u, hsurj, hker⟩, hphi, hgal⟩ := hB
  have hy := UpperTheory.evalEtaleFamily_mem_limit_of_reduced e he.red M j v c
  refine Exists.elim (hsurj ⟨_, hy⟩) fun h hh => ?_
  choose χ hχ using (galA_tA (K := K))
  letI iQ : Module (Acris l) (Pb.AL r M j) := (inferInstance : Module (per l K).A (Pb.AL r M j))
  have hz := chain1 (R := Acris l) (Q := Pb.AL r M j) (H := (M.HS true j).lim) (Γ := K.fixingSubgroup)
    (Mn := fun n => M.MH n j) l (tA l) (phiA l) galA (fun g => zA l (χ g)) (fun n => bl M j n) (fun g => Pb.galL M j g)
    (fun g n => M.galMH (IntermediateField.fixingSubgroupEquiv K g) n j) u s (f * N') (F.α M j) (F.galT M j)
    hker (fun g x n => hgal g x n) (fun n => evE e M j n v c) h hh hχ (phiA_iter_l _) (phiA_iterate_tA _)
    (fun g => phiA_iterate_zA _ _) (F.lin M hM j) (F.gal M hM j)
    (fun g => UpperTheory.galoisAction_evalEtaleFamily_exists_denominator B₀ e he M j s v c g (χ g) (hχ g) hinv)
  have hd := UpperTheory.galois_equivariant_tensor_descent_of_prime_power_units l (W := WittVector l r.k) (A := Pb.AW r) (C := B₀.C) (Γ := K.fixingSubgroup) (L := Pb.LW r M j)
    B₀.c (tA l) galA (fun g => (B₀.σ g).toRingHom) (fun g => zA l (χ g)) (F.galT M j) (F.α M j h) (u + s)
    (witt_fac r.k) (isUnit_l B₀) B₀.t_unit B₀.loc B₀.ker B₀.σ_c hC.1 hχ (fun g a y => F.galT_tmul M hM j g a y) hC.2 hz
  obtain ⟨a', b', y, hab⟩ := hd
  have key := keyStep hk hFr hρ F hPin y
  choose x hx1 hx2 using key
  refine ⟨a' + F.e M j + f * N' * u, b' + u, x, fun n => ⟨hx1 n, ?_⟩⟩
  have hc := chain2 (R := Acris l) (Q := Pb.AL r M j) (H := (M.HS true j).lim) (Mn := fun n => M.MH n j) l (tA l) (phiA l)
    (fun n => bl M j n) (fun x => Pb.phiL M j x) (fun n => phiH M.P n j) u s (f * N') (F.e M j) a' b' (F.α M j) (F.β M j) h
    ((1 : Pb.AW r) ⊗ₜ y) (fun n => evE e M j n v c) (fun n => evE e M j n v fun k => (phiA l)^[f * N'] (c k)) hh
    (phiA_iter_l _) (phiA_iterate_tA _) hab (F.fac M hM j h) (fun x n => hphi x n) (fun n a x => phi_iter_smul M.P n j _ a x)
    (fun n => UpperTheory.crisFrobenius_iterate_evalEtaleFamily e he.phi M j n _ v c) n
  exact hc.trans (congrArg _ (hx2 n))
end
end

section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
  {R : Per l K} {G : Model l K → Prop} {D : Dat R}

private theorem smul_toV {M : Model l K} {n : ℕ} (a : ℚ_[l]) (v : M.T n) :
    a • M.toV n v = (a ⊗ₜ[ℤ_[l]] v : ℚ_[l] ⊗[ℤ_[l]] M.T n) := by
  show a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] v : ℚ_[l] ⊗[ℤ_[l]] M.T n) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem V_induction {M : Model l K} {n : ℕ} {P : M.V n → Prop} (h0 : P 0)
    (h1 : ∀ (a : ℚ_[l]) (v : M.T n), P (a • M.toV n v)) (h2 : ∀ x y, P x → P y → P (x + y)) (w : M.V n) : P w := by
  refine TensorProduct.induction_on (motive := fun w : ℚ_[l] ⊗[ℤ_[l]] M.T n => P w) (show ℚ_[l] ⊗[ℤ_[l]] M.T n from w) h0 ?_ h2
  intro a v
  have := h1 a v
  rw [smul_toV] at this
  exact this

private structure IsVal (e : EMap G D) (b : BMap G D) (p : PMap G D) {M : Model l K} (a : D.Ch M) (n : ℕ)
    (C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)) : Prop where
  smul : ∀ (z : ℚ_[l]) (w : M.V n) φ, C (z • w) φ = R.q z * C w φ
  spec : ∀ (c : R.A) (v : M.T n) (x : (D.H a).N n), b.β a n x = c • e.e a n v →
    ∀ φ, p.κ a n x φ = R.i c * C (M.toV n v) φ

private theorem tB_pow_ne (hF : R.Facts) (m : ℕ) : R.i (R.t ^ m) ≠ 0 := by
  rw [map_pow]; exact pow_ne_zero _ hF.t_ne

private theorem exists_val (hF : R.Facts) (e : EMap G D) (b : BMap G D) (p : PMap G D) {M : Model l K} (hM : G M)
    (a : D.Ch M) (n : ℕ) : ∃ C, IsVal e b p a n C := by
  obtain ⟨N, hN⟩ := b.surj a hM n
  obtain ⟨m, hm⟩ := b.inj a hM n
  have hx : ∀ v, ∃ x, b.β a n x = R.t ^ N • e.e a n v := fun v => let ⟨x, _, h⟩ := hN (e.e a n v); ⟨x, h⟩
  choose xs hxs using hx
  have hκ : ∀ x x' : (D.H a).N n, b.β a n x = b.β a n x' → ∀ φ, p.κ a n x φ = p.κ a n x' φ := by
    intro x x' h φ
    have h1 := hm (x - x') (by rw [map_sub, h, sub_self])
    have h2 := congrArg (fun y => p.κ a n y φ) h1
    simp only [p.lin a hM, map_zero, AddMonoidHom.zero_apply, map_sub, AddMonoidHom.sub_apply] at h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (tB_pow_ne hF m))
  have hu := tB_pow_ne hF (R := R) N
  let c0 : M.T n → Module.Dual K (HdR M.q n) → R.B := fun v φ => (R.i (R.t ^ N))⁻¹ * p.κ a n (xs v) φ
  have spec0 : ∀ (c : R.A) (v : M.T n) (x : (D.H a).N n), b.β a n x = c • e.e a n v →
      ∀ φ, p.κ a n x φ = R.i c * c0 v φ := by
    intro c v x h φ
    have h1 := hκ (R.t ^ N • x) (c • xs v) (by
      rw [map_smul, map_smul, h, hxs, smul_smul, smul_smul, mul_comm]) φ
    rw [p.lin a hM, p.lin a hM] at h1
    simp only [c0]
    field_simp
    linear_combination h1
  have add0 : ∀ v v' φ, c0 (v + v') φ = c0 v φ + c0 v' φ := by
    intro v v' φ
    have := spec0 (R.t ^ N) (v + v') (xs v + xs v') (by rw [map_add, hxs, hxs, map_add, smul_add]) φ
    rw [map_add, AddMonoidHom.add_apply] at this
    simp only [c0]
    field_simp
    rw [this]; simp only [c0]; field_simp
  have sm0 : ∀ (z : ℤ_[l]) v φ, c0 (z • v) φ = R.q z * c0 v φ := by
    intro z v φ
    have := spec0 (R.t ^ N) (z • v) (R.z z • xs v) (by
      rw [map_smul, hxs, e.lin a hM, smul_smul, smul_smul, mul_comm]) φ
    rw [p.lin a hM, hF.thetaSetup_structureMap_comp] at this
    have h3 : c0 (z • v) φ = (R.i (R.t ^ N))⁻¹ * (R.q z * p.κ a n (xs v) φ) := by rw [this]; field_simp
    rw [h3]; simp only [c0]; ring
  let f : ℚ_[l] →+ M.T n →+ (Module.Dual K (HdR M.q n) → R.B) :=
    AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun v φ => R.q s * c0 v φ)
      (by intro v v'; funext φ; simp only [add0, Pi.add_apply, mul_add])) (by
        intro s s'; ext v φ; simp [add_mul])
  let C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B) := TensorProduct.liftAddHom f (by
    intro r s v; funext φ
    show R.q (r • s) * c0 v φ = R.q s * c0 (r • v) φ
    rw [sm0, Algebra.smul_def, map_mul]
    show R.q (r : ℚ_[l]) * _ * _ = _
    ring)
  have hC : ∀ (s : ℚ_[l]) (v : M.T n) φ, C (s • M.toV n v) φ = R.q s * c0 v φ := by
    intro s v φ
    rw [smul_toV]
    show (TensorProduct.liftAddHom f _ (s ⊗ₜ v)) φ = _
    rw [TensorProduct.liftAddHom_tmul]
    rfl
  have hC1 : ∀ (v : M.T n) φ, C (M.toV n v) φ = c0 v φ := by
    intro v φ
    have := hC 1 v φ
    rwa [one_smul, map_one, one_mul] at this
  refine ⟨C, ?_, ?_⟩
  · intro z w φ
    refine V_induction (P := fun w => C (z • w) φ = R.q z * C w φ) ?_ ?_ ?_ w
    · simp
    · intro s v
      rw [smul_smul, hC, hC, map_mul]; ring
    · intro x y hx hy
      rw [smul_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  · intro c v x h φ
    rw [hC1]; exact spec0 c v x h φ

private theorem exists_rep (e : EMap G D) (b : BMap G D) {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) :
    ∃ N : ℕ, ∀ v, ∃ x, b.β a n x = R.t ^ N • e.e a n v := by
  obtain ⟨N, hN⟩ := b.surj a hM n
  exact ⟨N, fun v => let ⟨x, _, h⟩ := hN (e.e a n v); ⟨x, h⟩⟩

private theorem act_toV {M : Model l K} {n : ℕ} (σ : K.fixingSubgroup) (v : M.T n) :
    M.act n σ (M.toV n v) = M.toV n (M.actT n σ v) := rfl

variable {e : EMap G D} {b : BMap G D} {p : PMap G D} {M : Model l K} {a : D.Ch M}

private theorem IsVal.equi {n : ℕ} {C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)} (hC : IsVal e b p a n C)
    (hF : R.Facts) (hL : D.Laws G) (hM : G M) (σ : K.fixingSubgroup) (w : M.V n) (φ) :
    C (M.act n σ w) φ = R.σ σ (C w φ) := by
  refine V_induction (P := fun w => C (M.act n σ w) φ = R.σ σ (C w φ)) (by simp) ?_ ?_ w
  · intro s v
    rw [map_smul, hC.smul, hC.smul, map_mul, hF.σ_q, act_toV]
    congr 1
    obtain ⟨N, hN⟩ := exists_rep e b hM a n
    obtain ⟨x, hx⟩ := hN v
    have h1 := hC.spec (R.σA σ (R.t ^ N)) (M.actT n σ v) ((D.H a).act n σ x) (by
      rw [b.act a hM, hx, hL.act_smul, e.act a hM]) φ
    rw [p.act a hM, hC.spec _ _ _ hx, map_mul, hF.i_σ] at h1
    exact (mul_left_cancel₀ ((map_ne_zero _).mpr (tB_pow_ne hF N)) h1).symm
  · intro x y hx hy
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]

private theorem IsVal.cup {i j : ℕ} {Ci : M.V i →+ (Module.Dual K (HdR M.q i) → R.B)}
    {Cj : M.V j →+ (Module.Dual K (HdR M.q j) → R.B)} {Cij : M.V (i + j) →+ (Module.Dual K (HdR M.q (i + j)) → R.B)}
    (hi : IsVal e b p a i Ci) (hj : IsVal e b p a j Cj) (hij : IsVal e b p a (i + j) Cij)
    (hF : R.Facts) (hL : D.Laws G) (hM : G M) (x : M.T i) (y : M.T j) (z : M.T (i + j)) (h : M.CupT x y z)
    {m m' : ℕ} (bb : Module.Basis (Fin m) K (HdR M.q i)) (bb' : Module.Basis (Fin m') K (HdR M.q j)) (φ) :
    Cij (M.toV _ z) φ = ∑ s, ∑ s', Ci (M.toV _ x) (bb.coord s) * Cj (M.toV _ y) (bb'.coord s') *
      R.o (φ (p.cupR M i j (bb s) (bb' s'))) := by
  obtain ⟨N, hN⟩ := exists_rep e b hM a i
  obtain ⟨N', hN'⟩ := exists_rep e b hM a j
  obtain ⟨X, hX⟩ := hN x
  obtain ⟨Y, hY⟩ := hN' y
  obtain ⟨Z, hZ⟩ := hL.cup_ex a X Y
  have h1 := b.cup a hM X Y Z hZ
  rw [hX, hY] at h1
  have h2 := hL.cup_uniq a _ _ _ _ h1 (hL.cup_smul a _ _ _ _ _ (e.cup a hM x y z h))
  have h3 := p.cup a hM X Y Z hZ bb bb' φ
  rw [hij.spec _ _ _ h2] at h3
  simp only [hi.spec _ _ _ hX, hj.spec _ _ _ hY] at h3
  rw [map_mul] at h3
  refine mul_left_cancel₀ (mul_ne_zero (tB_pow_ne hF N) (tB_pow_ne hF N')) (h3.trans ?_)
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem pow_rep (hS : EtSide G) (hL : D.Laws G) (hM : G M) (x : (D.H a).N 2) (v : M.T 2)
    (hx : b.β a 2 x = R.t • e.e a 2 v) (k : ℕ) (z : (D.H a).N (2 * k))
    (hz : IsPow (N := (D.H a).N) (D.H a).one (D.H a).cup x k z) :
    ∃ w : M.T (2 * k), b.β a (2 * k) z = R.t ^ k • e.e a (2 * k) w := by
  induction k with
  | zero =>
    obtain ⟨w, hw⟩ := e.one a hM
    exact ⟨w, by rw [pow_zero, one_smul]; exact hL.one_uniq a _ _ (b.one a hM z hz) hw⟩
  | succ k ih =>
    obtain ⟨y, hy, hc⟩ := hz
    obtain ⟨w, hw⟩ := ih y hy
    obtain ⟨w', hw'⟩ := hS.cup_ex M w v
    have h1 := b.cup a hM y x z hc
    rw [hw, hx] at h1
    refine ⟨w', ?_⟩
    have h2 := hL.cup_uniq a _ _ _ _ h1 (hL.cup_smul a _ _ _ _ _ (e.cup a hM w v w' hw'))
    rw [pow_succ]
    exact h2

private theorem IsVal.top {d : ℕ} {C : M.V (2 * d) →+ (Module.Dual K (HdR M.q (2 * d)) → R.B)} (hC : IsVal e b p a (2 * d) C)
    (hF : R.Facts) (hS : EtSide G) (hL : D.Laws G) (hM : G M) (hd : M.Conn d) : ∃ w φ, C w φ ≠ 0 := by
  obtain ⟨x, z, φ, hx, hz, hU⟩ := p.c1 a hM d hd
  obtain ⟨v, hv⟩ := e.c1 a hM
  have h1 := hL.first_chern_class_unique a _ _ (b.c1 a hM x hx) hv
  obtain ⟨w, hw⟩ := pow_rep hS hL hM x v h1 d z hz
  refine ⟨M.toV _ w, φ, fun h0 => ?_⟩
  obtain ⟨_, y, _, hy⟩ := hU
  rw [hC.spec _ _ _ hw, h0, mul_zero, zero_mul] at hy
  exact zero_ne_one hy

private theorem IsVal.van {n : ℕ} {C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)} (hC : IsVal e b p a n C)
    (hF : R.Facts) (hM : G M) {ι : Type} [Fintype ι] (v : ι → M.T n) (c : ι → R.A) (u : ℕ)
    (h : R.t ^ u • ∑ k, c k • e.e a n (v k) = 0) (ψ) : ∑ k, R.i (c k) * C (M.toV n (v k)) ψ = 0 := by
  obtain ⟨N, hN⟩ := exists_rep e b hM a n
  obtain ⟨m, hm⟩ := b.inj a hM n
  choose xs hxs using fun k => hN (v k)
  have h1 := hm (R.t ^ u • ∑ k, (c k • xs k)) (by
    simp only [map_smul, map_sum, hxs]
    simp only [smul_comm (c _) (R.t ^ N), ← Finset.smul_sum]
    rw [smul_comm, h, smul_zero])
  have h2 := congrArg (fun y => p.κ a n y ψ) h1
  simp only [p.lin a hM, map_zero, AddMonoidHom.zero_apply, map_sum, AddMonoidHom.finset_sum_apply,
    hC.spec _ _ _ (hxs _)] at h2
  have h3 := (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (tB_pow_ne hF m))).resolve_left (tB_pow_ne hF u)
  have h4 : R.i (R.t ^ N) * ∑ k, R.i (c k) * C (M.toV n (v k)) ψ = 0 := by
    rw [Finset.mul_sum, ← h3]
    exact Finset.sum_congr rfl fun _ _ => by ring
  exact (mul_eq_zero.mp h4).resolve_left (tB_pow_ne hF N)

private theorem inj_conn (hF : R.Facts) (hS : EtSide G) (hL : D.Laws G) (e : EMap G D) (b : BMap G D) (p : PMap G D)
    {M : Model l K} (hM : G M) {d : ℕ} (hd : M.Conn d) (a : D.Ch M) (j : ℕ) {ι : Type} [Fintype ι]
    (v : ι → M.T j) (c : ι → R.A) (u : ℕ) (h : R.t ^ u • ∑ k, c k • e.e a j (v k) = 0)
    (f : Module.Dual ℚ_[l] (M.V j)) : ∑ k, R.q (f (M.toV j (v k))) * R.i (c k) = 0 := by
  obtain ⟨hsub, hdual⟩ := hS.dual M hM d hd
  by_cases hj : 2 * d < j
  · have := hsub j hj
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Subsingleton.elim (M.toV j (v k)) 0, map_zero, map_zero, zero_mul]
  obtain ⟨j', hj'⟩ : ∃ j', j + j' = 2 * d := ⟨2 * d - j, by omega⟩
  obtain ⟨r, g, hspan, htrans, hfun⟩ := hdual j j' hj'
  choose C hC using fun n => exists_val hF e b p hM a n
  have htop : ∀ N, N = 2 * d → ∃ w φ, C N w φ ≠ 0 := by
    rintro _ rfl; exact (hC _).top hF hS hL hM hd
  obtain ⟨w, φ, hw⟩ := htop _ hj'
  have hg : ∃ s, C (j + j') (g s) φ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hw' : w ∈ Submodule.span ℚ_[l] (Set.range g) := by rw [hspan]; trivial
    refine hw (Submodule.span_induction (p := fun w _ => C (j + j') w φ = 0) ?_ (by simp) ?_ ?_ hw')
    · rintro _ ⟨s, rfl⟩; exact hcon s
    · intro x y _ _ hx hy; rw [map_add, Pi.add_apply, hx, hy, add_zero]
    · intro z x _ hx; rw [(hC _).smul, hx, mul_zero]
  obtain ⟨s₀, hs₀⟩ := hg
  have hall : ∀ s, C (j + j') (g s) φ ≠ 0 := by
    intro s h0
    obtain ⟨σ, z, hz, hact⟩ := htrans s s₀
    have h1 := (hC _).equi hF hL hM σ (g s) φ
    rw [hact, (hC _).smul, h0, map_zero] at h1
    exact (mul_ne_zero ((map_ne_zero _).mpr hz) hs₀) h1
  haveI := (p.fin M hM j).1
  haveI := (p.fin M hM j').1
  let bb := Module.finBasis K (HdR M.q j)
  let bb' := Module.finBasis K (HdR M.q j')
  have hf : f ∈ Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V j) | ∃ (s : Fin r) (y : M.T j'),
      ∀ x : M.T j, ∃ z, M.CupT x y z ∧ M.toV (j + j') z = f (M.toV j x) • g s} := by rw [hfun]; trivial
  refine Submodule.span_induction (p := fun f _ => ∑ k, R.q (f (M.toV j (v k))) * R.i (c k) = 0) ?_ (by simp) ?_ ?_ hf
  · rintro f ⟨s, y, hy⟩
    choose zs hz1 hz2 using fun k => hy (v k)
    have h1 : ∑ k, R.i (c k) * C (j + j') (M.toV _ (zs k)) φ = 0 := by
      simp only [fun k => (hC j).cup (hC j') (hC (j + j')) hF hL hM _ y _ (hz1 k) bb bb' φ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s₂ _ => ?_
      have h2 := (hC j).van hF hM v c u h (bb.coord s₁)
      calc _ = (∑ k, R.i (c k) * C j (M.toV j (v k)) (bb.coord s₁)) * (C j' (M.toV j' y) (bb'.coord s₂) *
              R.o (φ (p.cupR M j j' (bb s₁) (bb' s₂)))) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [h2, zero_mul]
    simp only [hz2, (hC _).smul] at h1
    have h3 : (∑ k, R.q (f (M.toV j (v k))) * R.i (c k)) * C (j + j') (g s) φ = 0 := by
      rw [Finset.sum_mul, ← h1]; exact Finset.sum_congr rfl fun _ _ => by ring
    exact (mul_eq_zero.mp h3).resolve_right (hall s)
  · intro x y _ _ hx hy
    simp only [LinearMap.add_apply, map_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  · intro z x _ hx
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]

private theorem toV_pullT {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (v : N.T n) :
    M.toV n (Model.pullT u hu n v) = Model.pullV u hu n (N.toV n v) := rfl

theorem injAbs : UpperTheory.Ru.crystallineComparison.InjAbs := by
  intro l _ K R G D hF hS hL e b p M hM a j ι _ v c u h f
  obtain ⟨r, P, d, uu, hu, hP, hinj⟩ := hS.comp M hM
  have hs : ∀ s (f' : Module.Dual ℚ_[l] ((P s).V j)),
      ∑ k, R.q (f' (Model.pullV (uu s) (hu s) j (M.toV j (v k)))) * R.i (c k) = 0 := by
    intro s f'
    obtain ⟨a₀⟩ := hL.ch (P s) (hP s).1
    obtain ⟨a', _, ⟨m⟩⟩ := hL.refine (P s) M (uu s) (hu s) (hP s).1 hM a₀ a
    have := inj_conn hF hS hL e b p (hP s).1 (hP s).2 a' j (fun k => Model.pullT (uu s) (hu s) j (v k)) c u (by
      have h1 := congrArg (D.pullA m j) h
      simpa only [map_smul, map_sum, map_zero, ← e.nat m (hP s).1 hM] using h1) f'
    simpa only [toV_pullT] using this
  let L : M.V j →ₗ[ℚ_[l]] ∀ s, (P s).V j := LinearMap.pi fun s => Model.pullV (uu s) (hu s) j
  have hk : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot'.2 fun w hw => hinj j w fun s => congrFun hw s
  obtain ⟨g, hg⟩ := L.exists_leftInverse_of_injective hk
  let f' : ∀ s, Module.Dual ℚ_[l] ((P s).V j) := fun s => (f ∘ₗ g) ∘ₗ LinearMap.single ℚ_[l] (fun s => (P s).V j) s
  have hf : ∀ w, f w = ∑ s, f' s (Model.pullV (uu s) (hu s) j w) := by
    intro w
    have h1 : g (L w) = w := LinearMap.congr_fun hg w
    conv_lhs => rw [← h1, ← Finset.univ_sum_single (L w), map_sum, map_sum]
    rfl
  simp only [hf, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun s _ => hs s (f' s)

end UpperTheory.Ru.crystallineComparison
end
end

section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

private theorem UpperTheory.Ru.crystallineComparison.eq_zero_of_coord {F V C : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup C] [Module F C] (w : V ⊗[F] C)
    (h : ∀ f : Module.Dual F V, TensorProduct.lid F C (LinearMap.rTensor C f w) = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext i
  have key : ∀ w : V ⊗[F] C, (TensorProduct.equivFinsuppOfBasisLeft b w) i =
      TensorProduct.lid F C (LinearMap.rTensor C (b.coord i) w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp [hx, hy]
  rw [key, h]
  rfl

theorem UpperTheory.Ru.crystallineComparison.injOf :
    UpperTheory.Ru.crystallineComparison.InjOf := by
  intro l _ K B₀ ι hι hc hq G Amp hF hE hL e e' hB hP hcomp M hM j κ _ v c u hu
  obtain ⟨a⟩ := hL.ch M hM
  have h0 : (per l K).t ^ u • ∑ k, (show (per l K).A from c k) • e'.e a j (v k) = 0 := by
    change ((UpperTheory.Ru.crystallineComparison.tA l ^ u • ∑ k, c k • (show (M.MS j).lim from e'.e a j (v k)) : (M.MS j).lim)) = 0
    apply Subtype.ext
    funext n
    have := hu n
    simp only [UpperTheory.Ru.crystallineComparison.evE] at this
    simpa [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, hcomp] using this
  have h1 := UpperTheory.Ru.crystallineComparison.injAbs l K (per l K) G (dat Amp) hF hE hL e' hB hP M hM a j κ v c u h0
  apply UpperTheory.Ru.crystallineComparison.eq_zero_of_coord
  intro f
  apply hι
  have h2 := h1 f
  simp only [UpperTheory.Ru.crystallineComparison.vec, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, pow_zero, mul_one, map_zero]
  simp only [Algebra.smul_def, map_mul, hq, hc]
  exact h2
end
end

section
open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.ePin :
    ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (G : Model l K → Prop) (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (e : E.EtFam l K), e.Good → ∃ e' : EMap G (dat Amp), ∀ (M : Model l K) (a : (dat Amp).Ch M) (j : ℕ) (v : M.T j) (n : ℕ), (show (M.MS j).lim from e'.e a j v).1 n = e M n j (v.lev n) := by
  intro l _ K G Amp e he
  refine ⟨{
    e := fun {M} _ j => GlueE.eMap e he.red M j
    lin := fun {M} _ _ j z v => GlueE.eMap_lin e he.red M j (per l K).z z v
    act := fun {M} _ _ j _ v => GlueE.eMap_act e he.red he.equi M j _ v
    phi := fun {M} _ _ j v => GlueE.eMap_phi e he.red he.phi M j v
    nat := fun {_ _ u hu _ _} _ _ _ j v => GlueE.eMap_nat e he.red he.nat u hu j v
    cup := fun {M} _ _ _ _ x y z h => GlueE.eMap_cup e he.red he.cup M x y z h
    one := fun {M} _ _ => GlueE.eMap_one e he.red he.one M
    c1 := fun {M} a _ => GlueE.etale_map_first_chern e he.red he.c1 M a.1 (per l K).t rfl }, ?_⟩
  intro M a j v n
  rfl
end

section
open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Ru.crystallineComparison.PBIota

open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime]

private theorem galCp_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[l] →+* ℂ_[l]) = galCp τ :=
  RingHom.ext fun x => congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]) x

private theorem galMap_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (galCp_congr σ τ h) _ _

private theorem galAway_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galAway σ = ACris.galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : AInf ℂ_[l] l)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, ACris.galAway_algebraMap, ACris.galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])

private theorem galCris_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galCris σ = ACris.galCris τ := by
  have e : ACris.galZero σ = ACris.galZero τ := RingHom.ext fun y => Subtype.ext (by
    rw [ACris.coe_galZero, ACris.coe_galZero, galAway_congr σ τ h])
  rw [ACris.galCris, ACris.galCris, e]

private theorem iC_injective : Function.Injective (iC l) :=
  (IsFractionRing.injective (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)).comp ACris.iota_injective

private theorem iC_galA {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (g : K.fixingSubgroup)
    (a : Acris l) : iC l (galA g a) = Formalism.Per6.σD g.1 (iC l a) := by
  have e : galA g = ACris.galCris (Formalism.Per6.toBot g.1) :=
    galCris_congr _ _ fun _ => rfl
  rw [e]
  exact PositivityTheory.LocInh.GaloisCommutant.cD_galCris g.1 a

private theorem iC_zA (z : ℤ_[l]) : iC l (zA l z) = qQ l z := by
  change algebraMap _ _ (ACris.iota ℂ_[l] l _) = algebraMap _ _ (algebraMap ℚ_[l] _ _)
  exact congrArg _ (ACris.iota_padicInt z)

private theorem exists_lift {A C E : Type} [CommRing A] [CommRing C] [Field E] (t : A) (c : A →+* C)
    (i : A →+* E) (hu : IsUnit (c t)) (loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a)
    (ker : ∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0) (hi : Function.Injective i) (ht : i t ≠ 0) :
    ∃ ι : C →+* E, Function.Injective ι ∧ ∀ a, ι (c a) = i a := by
  letI : Algebra A C := c.toAlgebra
  have hc : ∀ a, algebraMap A C a = c a := fun _ => rfl
  haveI : IsLocalization (Submonoid.powers t) C :=
    { map_units := by
        rintro ⟨_, r, rfl⟩
        rw [hc, map_pow]
        exact hu.pow r
      surj := fun x => by
        obtain ⟨r, a, h⟩ := loc x
        refine ⟨⟨a, ⟨t ^ r, r, rfl⟩⟩, ?_⟩
        change x * algebraMap A C (t ^ r) = algebraMap A C a
        rw [hc, hc, map_pow, mul_comm, h]
      exists_of_eq := fun {x y} h => by
        rw [hc, hc] at h
        obtain ⟨r, hr⟩ := ker (x - y) (by rw [map_sub, h, sub_self])
        refine ⟨⟨t ^ r, r, rfl⟩, ?_⟩
        change t ^ r * x = t ^ r * y
        rw [mul_sub, sub_eq_zero] at hr
        exact hr }
  have hm : ∀ y : Submonoid.powers t, IsUnit (i y) := by
    rintro ⟨_, r, rfl⟩
    change IsUnit (i (t ^ r))
    rw [map_pow]
    exact (IsUnit.mk0 _ ht).pow r
  let ι : C →+* E := IsLocalization.lift (M := Submonoid.powers t) hm
  have hι : ∀ a, ι (c a) = i a := fun a => IsLocalization.lift_eq (M := Submonoid.powers t) hm a
  refine ⟨ι, (injective_iff_map_eq_zero ι).2 fun x hx => ?_, hι⟩
  obtain ⟨r, a, h⟩ := loc x
  have h1 : i a = 0 := by rw [← hι, ← h, map_mul, hx, mul_zero]
  have h2 : a = 0 := hi (by rw [h1, map_zero])
  rw [h2, map_zero] at h
  exact (hu.pow r).mul_right_eq_zero.1 h

private theorem lift_comm {A C E : Type} [CommRing A] [CommRing C] [Field E] (t : A) (c : A →+* C)
    (i : A →+* E) (loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a) (ht : i t ≠ 0)
    (ι : C →+* E) (hι : ∀ a, ι (c a) = i a) (s : C →+* C) (u : A →+* A) (d : E →+* E)
    (hs : ∀ a, s (c a) = c (u a)) (hd : ∀ a, i (u a) = d (i a)) (x : C) : ι (s x) = d (ι x) := by
  obtain ⟨r, a, h⟩ := loc x
  have h1 : d (i t) ^ r * ι (s x) = d (i a) := by
    have := congrArg (fun y => ι (s y)) h
    simp only [map_mul, map_pow, hs, hι, hd] at this
    exact this
  have h2 : i t ^ r * ι x = i a := by
    have := congrArg ι h
    simp only [map_mul, map_pow, hι] at this
    exact this
  rw [← h2, map_mul, map_pow] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ ((map_ne_zero d).2 ht)) h1

private theorem q_ext {E : Type} [Field E] (f q : ℚ_[l] →+* E)
    (h : ∀ z : ℤ_[l], f (z : ℚ_[l]) = q (z : ℚ_[l])) : f = q :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext h)

end UpperTheory.Ru.crystallineComparison.PBIota

open UpperTheory.Ru.crystallineComparison.PBIota in
theorem UpperTheory.Ru.crystallineComparison.pbIota :
    ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (B₀ : PB l K), ∃ ι : B₀.C →+* (per l K).B, Function.Injective ι ∧ (∀ a, ι (B₀.c a) = (per l K).i a) ∧ (∀ z, ι (algebraMap ℚ_[l] B₀.C z) = (per l K).q z) ∧ ∀ g x, ι (B₀.σ g x) = (per l K).σ g (ι x) := by
  intro l _ K B₀
  have ht0 : DeRhamPotentiallySemistable.DRPst.iC l (tA l) ≠ 0 := (period_ring_base.isUnit_image_period l).ne_zero
  obtain ⟨ι, hinj, hι⟩ := exists_lift (tA l) B₀.c (DeRhamPotentiallySemistable.DRPst.iC l) B₀.t_unit B₀.loc B₀.ker
    iC_injective ht0
  refine ⟨ι, hinj, hι, fun z => ?_, fun g x => ?_⟩
  · exact RingHom.congr_fun (q_ext (ι.comp (algebraMap ℚ_[l] B₀.C)) (DeRhamPotentiallySemistable.DRPst.qQ l) fun z =>
      (congrArg ι (B₀.z_c z)).trans ((hι _).trans (iC_zA z))) z
  · exact lift_comm (tA l) B₀.c (DeRhamPotentiallySemistable.DRPst.iC l) B₀.loc ht0 ι hι (B₀.σ g : B₀.C →+* B₀.C)
      (galA g) (Formalism.Per6.σD g.1 : Formalism.Per6.BdR l ≃+* Formalism.Per6.BdR l).toRingHom (B₀.σ_c g) (iC_galA g) x
end

section
set_option maxSynthPendingDepth 1
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison GroundTheory.PAdicHodge

namespace UpperTheory.Ru.crystallineComparison.PBI

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section

set_option backward.isDefEq.respectTransparency false

private theorem coe_sub_oc (a b : OC l) : ((a - b : OC l) : ℂ_[l]) = (a : ℂ_[l]) - (b : ℂ_[l]) := rfl

private theorem rho_zero (r : Res l K) (d : OK l K) (h : ‖((okToOC l K d : OC l) : ℂ_[l])‖ < 1) : r.ρ d = 0 := by
  by_contra h0
  have hu : IsUnit (r.s (r.ρ d)) := (IsUnit.mk0 _ h0).map r.s
  have h1 := (IsPerfectoidField.isUnit_iff_norm_untilt (K := ℂ_[l]) l).1 hu
  have h2 := r.hs d
  rw [coe_sub_oc] at h2
  have h3 : ‖((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l])‖ < 1 := by
    have e : ((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l]) =
        (((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l]) - ((okToOC l K d : OC l) : ℂ_[l])) + ((okToOC l K d : OC l) : ℂ_[l]) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h)
  exact absurd h1 h3.ne

private theorem pow_fix (r : Res l K) (a : r.k) : ∃ f : ℕ, 0 < f ∧ a ^ l ^ f = a := by
  obtain ⟨x, rfl⟩ := r.surj a
  have hc : ‖((x : K) : PadicAlgCl l)‖ ≤ 1 := mem_normInteger.1 x.2
  obtain ⟨k₀, k₁, hlt, hn⟩ := exists_lt_norm_pow_sub_lt hc one_pos (fun k => l ^ k)
  have hd := rho_zero r (x ^ l ^ k₁ - x ^ l ^ k₀) (by
    have e : ((okToOC l K (x ^ l ^ k₁ - x ^ l ^ k₀) : OC l) : ℂ_[l]) =
        clToC l (((x : K) : PadicAlgCl l) ^ l ^ k₁ - ((x : K) : PadicAlgCl l) ^ l ^ k₀) := by
      simp [okToOC]
    rw [e, norm_clToC]
    exact hn)
  rw [map_sub, map_pow, map_pow, sub_eq_zero] at hd
  refine ⟨k₁ - k₀, by omega, ?_⟩
  have h0 : ((r.ρ x) ^ l ^ (k₁ - k₀) - r.ρ x) ^ l ^ k₀ = 0 := by
    rw [sub_pow_char_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hlt.le, hd, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h0)

private theorem untilt_pow' (x : Ob l) (n : ℕ) :
    ((PreTilt.untilt (x ^ n) : OC l) : ℂ_[l]) = ((PreTilt.untilt x : OC l) : ℂ_[l]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, untilt_mul]; simp [ih]

private theorem gfix (r : Res l K) (g : Gal(PadicAlgCl l/K)) (a : r.k) : EigenWitt.galFlat g (r.s a) = r.s a := by
  obtain ⟨f, hf, haf⟩ := pow_fix r a
  obtain ⟨x, rfl⟩ := r.surj a
  have hq : 1 < l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt
  have hu : (r.s (r.ρ x)) ^ l ^ f = r.s (r.ρ x) := by rw [← map_pow, haf]
  have hv : (EigenWitt.galFlat g (r.s (r.ρ x))) ^ l ^ f = EigenWitt.galFlat g (r.s (r.ρ x)) := by
    rw [← map_pow, hu]
  by_contra hne
  obtain ⟨u, hudef⟩ : ∃ u, u = r.s (r.ρ x) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v, v = EigenWitt.galFlat g u := ⟨_, rfl⟩
  rw [← hudef] at hu hv hne
  rw [← hvdef] at hv hne
  have he0 : v - u ≠ 0 := sub_ne_zero.2 hne
  have hee : (v - u) ^ l ^ f = v - u := by rw [sub_pow_char_pow, hu, hv]
  have hc : ‖((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])‖ < 1 := by
    have := r.hs x
    rw [coe_sub_oc, ← hudef] at this
    exact this
  have hsv : ((PreTilt.untilt v : OC l) : ℂ_[l]) = g • ((PreTilt.untilt u : OC l) : ℂ_[l]) := by
    rw [hvdef]; exact AInf.coe_untilt_gal g u
  have hgx : g • ((okToOC l K x : OC l) : ℂ_[l]) = ((okToOC l K x : OC l) : ℂ_[l]) :=
    congrArg Subtype.val (galOC_okToOC g x)
  have hc' : ‖((PreTilt.untilt v : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])‖ < 1 := by
    rw [hsv, ← hgx, ← smul_sub]
    have h5 := norm_galCp g (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l]))
    exact (show ‖g • (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l]))‖ = _ from h5).trans_lt hc
  have hl : ‖(l : ℂ_[l])‖ < 1 := norm_natCast_p_lt_one
  have h1 := norm_untilt_add_sub_le (K := ℂ_[l]) (p := l) (v - u) u
  rw [sub_add_cancel] at h1
  have h2 : ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ < 1 := by
    have e : ((PreTilt.untilt (v - u) : OC l) : ℂ_[l]) =
        (((PreTilt.untilt v : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])) -
        (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])) -
        (((PreTilt.untilt v : OC l) : ℂ_[l]) - (((PreTilt.untilt (v - u) : OC l) : ℂ_[l]) + ((PreTilt.untilt u : OC l) : ℂ_[l]))) := by ring
    rw [e]
    refine (norm_sub_le_max_of_ultrametric _ _).trans_lt (max_lt ((norm_sub_le_max_of_ultrametric _ _).trans_lt (max_lt hc' hc)) (h1.trans_lt hl))
  have h3 : ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ ^ l ^ f = ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ := by
    rw [← norm_pow, ← untilt_pow', hee]
  have h4 : 0 < ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ := by
    refine norm_pos_iff.2 fun h => he0 ((IsPerfectoidField.untilt_eq_zero_iff (K := ℂ_[l]) l).1 (Subtype.ext h))
  exact absurd h3 (pow_lt_self_of_lt_one₀ h4 h2 hq).ne

private theorem wexp {k : Type} [Field k] [CharP k l] [PerfectRing k l] (τ : WittVector l k →+* OC l) (Z : Set (OC l))
    (hstep : ∀ x ∈ Z, ∃ (a : k) (x' : OC l), x' ∈ Z ∧ x = τ (WittVector.teichmuller l a) + (l : OC l) * x') :
    ∀ x ∈ Z, ∃ w, τ w = x := by
  have hs : ∀ x : Z, ∃ (a : k) (x' : Z), (x : OC l) = τ (WittVector.teichmuller l a) + (l : OC l) * x' := fun x => by
    obtain ⟨a, x', h, e⟩ := hstep x x.2
    exact ⟨a, ⟨x', h⟩, e⟩
  choose A N hAN using hs
  let E : Z → WittVector l k := fun x => WittVector.mk l (fun i => A (N^[i] x) ^ l ^ i)
  have hcoeff : ∀ x i, (E x).coeff i = A (N^[i] x) ^ l ^ i := fun x i => rfl
  have hE : ∀ x, E x = WittVector.teichmuller l (A x) + (l : WittVector l k) * E (N x) := by
    intro x
    rw [mul_comm (l : WittVector l k), ← WittVector.verschiebung_frobenius]
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · cases n with
      | zero => simp [hcoeff, WittVector.teichmuller_coeff_zero]
      | succ n =>
        rw [WittVector.teichmuller_coeff_pos _ _ _ (Nat.succ_pos n), WittVector.verschiebung_coeff_succ,
          WittVector.coeff_frobenius_charP, hcoeff, hcoeff, zero_add, Function.iterate_succ_apply, pow_succ, pow_mul]
    · intro n
      cases n with
      | zero => right; simp
      | succ n => left; exact WittVector.teichmuller_coeff_pos _ _ _ (Nat.succ_pos n)
  have hdiv : ∀ (n : ℕ) (x : Z), ∃ y : OC l, (x : OC l) - τ (E x) = (l : OC l) ^ n * y := by
    intro n
    induction n with
    | zero => exact fun x => ⟨(x : OC l) - τ (E x), by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := ih (N x)
      refine ⟨y, ?_⟩
      have h1 := hAN x
      have h2 : τ (E x) = τ (WittVector.teichmuller l (A x)) + (l : OC l) * τ (E (N x)) := by
        conv_lhs => rw [hE x]
        rw [map_add, map_mul, map_natCast]
      rw [h2, h1, pow_succ']
      linear_combination (l : OC l) * hy
  intro x hx
  refine ⟨E ⟨x, hx⟩, ?_⟩
  by_contra hne
  have hpos : 0 < ‖((x - τ (E ⟨x, hx⟩) : OC l) : ℂ_[l])‖ :=
    norm_pos_iff.2 fun h => hne (sub_eq_zero.1 (Subtype.ext h)).symm
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (norm_natCast_p_lt_one (p := l))
  obtain ⟨y, hy⟩ := hdiv n ⟨x, hx⟩
  have h1 : ‖((x - τ (E ⟨x, hx⟩) : OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n := by
    have hy' : x - τ (E ⟨x, hx⟩) = (l : OC l) ^ n * y := hy
    rw [hy']
    have e : (((l : OC l) ^ n * y : OC l) : ℂ_[l]) = (l : ℂ_[l]) ^ n * (y : ℂ_[l]) := by simp
    rw [e, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (mem_normInteger.1 y.2)
  exact absurd h1 (not_le.2 hn)

end

local notation "hE" => (untilt_epsilon (p := l))
local notation "hZ" => (untilt_frobeniusEquiv_symm_epsilon_ne_one (p := l))

variable (l) in
private def fB : Acris l →+* ACris.BCris (untilt_epsilon (p := l)) :=
  (algebraMap (ACris.BCrisPlus ℂ_[l] l) (ACris.BCris (untilt_epsilon (p := l)))).comp
    (algebraMap (Acris l) (ACris.BCrisPlus ℂ_[l] l))

private theorem iB_fB (a : Acris l) : ACris.iotaB hE hZ (fB l a) = DeRhamPotentiallySemistable.DRPst.iC l a := by
  change ACris.iotaB hE hZ (algebraMap (ACris.BCrisPlus ℂ_[l] l) _ (algebraMap (Acris l) _ a)) = _
  rw [ACris.iotaB_algebraMap, ACris.iotaPlus_algebraMap]
  rfl

private theorem iC_inj : Function.Injective (DeRhamPotentiallySemistable.DRPst.iC l) :=
  (IsFractionRing.injective (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l)).comp
    (ACris.iota_injective (K := ℂ_[l]) (p := l))

private theorem fB_t_unit : IsUnit (fB l (tA l)) :=
  IsLocalization.Away.algebraMap_isUnit (S := ACris.BCris (untilt_epsilon (p := l)))
    (algebraMap (ACris.ACris ℂ_[l] l) (ACris.BCrisPlus ℂ_[l] l) (ACris.periodT (untilt_epsilon (p := l))))

private theorem iC_t_unit : IsUnit (DeRhamPotentiallySemistable.DRPst.iC l (tA l)) := by
  rw [← iB_fB]
  exact fB_t_unit.map _

private theorem galB_fB (σ : Gal(PadicAlgCl l/K)) (a : Acris l) :
    ACris.galB hE σ (fB l a) = fB l (ACris.galCris σ a) := by
  change ACris.galB hE σ (algebraMap (ACris.BCrisPlus ℂ_[l] l) _ (algebraMap (Acris l) _ a)) = _
  rw [ACris.galB_algebraMap]
  exact congrArg _ (ACris.galPlus_algebraMap σ a)

private theorem galCris_w (r : Res l K) (σ : Gal(PadicAlgCl l/K)) (w : WittVector l r.k) :
    ACris.galCris σ (r.w w) = r.w w := by
  have h : σ • (WittVector.map r.s w) = WittVector.map r.s w := by
    ext n
    rw [AInf.gal_smul_coeff, WittVector.map_coeff]
    exact gfix r σ _
  have h2 := ACris.gal_smul_algebraMap σ (WittVector.map r.s w)
  rw [h] at h2
  exact h2

private def tau (r : Res l K) : WittVector l r.k →+* OC l :=
  (WittVector.fontaineTheta (OC l) l).comp (WittVector.map r.s)

private theorem tau_teich (r : Res l K) (a : r.k) :
    tau r (WittVector.teichmuller l a) = PreTilt.untilt (r.s a) := by
  rw [tau, RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]

private theorem hT [FiniteDimensional ℚ_[l] K] (r : Res l K) (w : WittVector l r.k) :
    ∃ k ∈ maxUnramified l K,
      DeRhamPotentiallySemistable.DRPst.iC l (r.w w) = algebraMap (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l) (algClToBdR l k) ∧
      clToC l k = ((tau r w : OC l) : ℂ_[l]) := by
  obtain ⟨k, hk, h⟩ := ACris.bCris_fixed_mem_maxUnramified hE hZ (K := K) (fB l (r.w w)) (fun σ => by
    rw [galB_fB, galCris_w])
  rw [iB_fB] at h
  refine ⟨k, hk, h, ?_⟩
  have h1 : ACris.iota ℂ_[l] l (r.w w) = algClToBdR l k :=
    IsFractionRing.injective (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l) h
  have h2 := congrArg (thetaAlgHom l) h1
  rw [thetaAlgHom_algClToBdR] at h2
  have h3 : r.w w = algebraMap (Ainf l) (Acris l) (WittVector.map r.s w) := rfl
  rw [h3, ACris.iota_algebraMap] at h2
  have h4 : thetaAlgHom l (wittToBDeRhamPlus (normInteger ℂ_[l]) l (WittVector.map r.s w)) = ((tau r w : OC l) : ℂ_[l]) :=
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus l (WittVector.map r.s w)
  exact h2.symm.trans h4

private theorem pullback_fin_relation {A F D P : Type*} [CommRing A] [CommRing F] [CommRing D] [CommRing P] (f : A →+* F) (j : F →+* D)
    (i : A →+* D) (q : P →+* D) (hji : ∀ u, j (f u) = i u) {t a W : A} {T : F} {n e L : ℕ} {k : P}
    (hT : f t * T = 1) (hk : j (f a * T ^ n) = q k) (hW : i W = q ((L : P) ^ e * k)) :
    i ((L : A) ^ e * a) = i (t ^ n * W) := by
  have h1 : i a = q k * i t ^ n := by
    rw [← hk, ← hji a, ← hji t, ← map_pow, ← map_mul, mul_assoc, ← mul_pow, mul_comm T, hT, one_pow, mul_one]
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, hW, h1, map_mul, map_pow, map_natCast]
  ring

private theorem fin2 {A C : Type*} [CommRing A] [CommRing C] (c : A →+* C) {t a W : A} {x : C} {n e L : ℕ}
    (ut : IsUnit (c t ^ n)) (hna : c t ^ n * x = c a) (hA : (L : A) ^ e * a = t ^ n * W) :
    (L : C) ^ e * x = c W := by
  apply ut.mul_left_cancel
  calc c t ^ n * ((L : C) ^ e * x) = (L : C) ^ e * (c t ^ n * x) := by ring
    _ = c ((L : A) ^ e * a) := by rw [hna, map_mul, map_pow, map_natCast]
    _ = c (t ^ n * W) := by rw [hA]
    _ = c t ^ n * c W := by rw [map_mul, map_pow]

private theorem fix_aux {A F : Type*} [CommRing A] [CommRing F] (f : A →+* F) (G : F →+* F) (s : A →+* A)
    {t a : A} {T : F} {n : ℕ} (hG : ∀ u, G (f u) = f (s u)) (hT : f t * T = 1)
    (I1 : s a * t ^ n = a * s t ^ n) : G (f a * T ^ n) = f a * T ^ n := by
  have hs : f (s t) * G T = 1 := by
    rw [← hG, ← map_mul, hT, map_one]
  have I2 := congrArg f I1
  simp only [map_mul, map_pow] at I2
  rw [map_mul, map_pow, hG]
  calc f (s a) * G T ^ n = f (s a) * G T ^ n * (f t * T) ^ n := by rw [hT, one_pow, mul_one]
    _ = (f (s a) * f t ^ n) * (G T ^ n * T ^ n) := by rw [mul_pow]; ring
    _ = f a * f (s t) ^ n * (G T ^ n * T ^ n) := by rw [I2]
    _ = f a * T ^ n * (f (s t) * G T) ^ n := by rw [mul_pow]; ring
    _ = f a * T ^ n := by rw [hs, one_pow, mul_one]

private theorem hK [FiniteDimensional ℚ_[l] K] (r : Res l K) {k : PadicAlgCl l} (hk : k ∈ maxUnramified l K) (h1 : ‖k‖ ≤ 1) :
    ∃ w : WittVector l r.k, DeRhamPotentiallySemistable.DRPst.iC l (r.w w) =
      algebraMap (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l) (algClToBdR l k) := by
  let Z : Set (OC l) := {x | ∃ k ∈ maxUnramified l K, (x : ℂ_[l]) = clToC l k}
  have hstep : ∀ x ∈ Z, ∃ (a : r.k) (x' : OC l), x' ∈ Z ∧
      x = tau r (WittVector.teichmuller l a) + (l : OC l) * x' := by
    rintro x ⟨k, hk, hx⟩
    have hk1 : ‖k‖ ≤ 1 := by
      rw [← norm_clToC, ← hx]
      exact mem_normInteger.1 x.2
    have hkK : k ∈ K := (mem_maxUnramified.1 hk).1
    let xo : OK l K := ⟨⟨k, hkK⟩, mem_normInteger.2 hk1⟩
    obtain ⟨k₀, hk₀, -, hk₀τ⟩ := hT r (WittVector.teichmuller l (r.ρ xo))
    rw [tau_teich] at hk₀τ
    have hlt : ‖k - k₀‖ < 1 := by
      have h2 := r.hs xo
      rw [coe_sub_oc, ← hk₀τ] at h2
      have e : ((okToOC l K xo : OC l) : ℂ_[l]) = clToC l k := rfl
      rw [e, ← map_sub, norm_clToC, norm_sub_rev] at h2
      exact h2
    have hy : k - k₀ ∈ maxUnramified l K := sub_mem hk hk₀
    have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    have hy' : (k - k₀) / (l : PadicAlgCl l) ∈ maxUnramified l K := div_mem hy (natCast_mem _ l)
    have hn : ‖(k - k₀) / (l : PadicAlgCl l)‖ ≤ 1 := by
      by_cases h0 : k - k₀ = 0
      · simp [h0]
      obtain ⟨D, hD⟩ := ACris.exists_norm_eq_zpow_maxUnramified (K := K) (x := ⟨k - k₀, hy⟩)
        (fun h => h0 (congrArg Subtype.val h))
      have hD' : ‖k - k₀‖ = ‖(l : PadicAlgCl l)‖ ^ D := hD
      have hlpos := ACris.norm_p_algCl_pos (p := l)
      have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := norm_natCast_p_algCl_lt_one
      have hD1 : 1 ≤ D := by
        by_contra hcon
        have h3 : D ≤ 0 := by omega
        have h4 : 1 ≤ ‖(l : PadicAlgCl l)‖ ^ D := one_le_zpow_of_nonpos₀ hlpos hl1.le h3
        rw [hD'] at hlt
        linarith
      rw [norm_div, hD', div_le_one hlpos]
      calc ‖(l : PadicAlgCl l)‖ ^ D ≤ ‖(l : PadicAlgCl l)‖ ^ (1 : ℤ) :=
            zpow_le_zpow_right_of_le_one₀ hlpos hl1.le hD1
        _ = ‖(l : PadicAlgCl l)‖ := zpow_one _
    refine ⟨r.ρ xo, ⟨clToC l ((k - k₀) / (l : PadicAlgCl l)), mem_normInteger.2 (by rw [norm_clToC]; exact hn)⟩,
      ⟨_, hy', rfl⟩, ?_⟩
    apply Subtype.ext
    rw [tau_teich]
    change (x : ℂ_[l]) = ((PreTilt.untilt (r.s (r.ρ xo)) : OC l) : ℂ_[l]) +
      (l : ℂ_[l]) * clToC l ((k - k₀) / (l : PadicAlgCl l))
    rw [hx, ← hk₀τ, ← map_natCast (clToC l) l, ← map_mul, ← map_add]
    congr 1
    field_simp
    ring
  have hx : (⟨clToC l k, mem_normInteger.2 (by rw [norm_clToC]; exact h1)⟩ : OC l) ∈ Z := ⟨k, hk, rfl⟩
  obtain ⟨w, hw⟩ := wexp (tau r) Z hstep _ hx
  obtain ⟨k₁, -, h2, h3⟩ := hT r w
  rw [hw] at h3
  have e : k₁ = k := (clToC l).injective h3
  exact ⟨w, e ▸ h2⟩

private theorem mainC [FiniteDimensional ℚ_[l] K] (B₀ : PB l K) (r : Res l K) : InvC B₀ r := by
  refine ⟨fun g w => galCris_w r _ w, fun x hx => ?_⟩
  have hcinj : ∀ u v : Acris l, B₀.c u = B₀.c v → u = v := by
    intro u v h
    obtain ⟨m, hm⟩ := B₀.ker (u - v) (by rw [map_sub, h, sub_self])
    have h1 := congrArg (DeRhamPotentiallySemistable.DRPst.iC l) hm
    rw [map_mul, map_pow, map_zero] at h1
    have h2 := ((iC_t_unit.pow m).mul_right_eq_zero).1 h1
    rw [map_sub, sub_eq_zero] at h2
    exact iC_inj h2
  obtain ⟨n, a, hna⟩ := B₀.loc x
  obtain ⟨T, hT1⟩ := fB_t_unit (l := l) |>.exists_right_inv
  have hy : ∀ σ : Gal(PadicAlgCl l/K), ACris.galB hE σ (fB l a * T ^ n) = fB l a * T ^ n := by
    intro σ
    have hσ : IntermediateField.fixingSubgroupEquiv K ((IntermediateField.fixingSubgroupEquiv K).symm σ) = σ :=
      MulEquiv.apply_symm_apply _ σ
    have hsc : ∀ u, B₀.σ ((IntermediateField.fixingSubgroupEquiv K).symm σ) (B₀.c u) = B₀.c (ACris.galCris σ u) := by
      intro u
      rw [B₀.σ_c, galA, hσ]
    have hg := hx ((IntermediateField.fixingSubgroupEquiv K).symm σ)
    refine fix_aux (fB l) (ACris.galB hE σ) (ACris.galCris σ) (galB_fB σ) hT1 (hcinj _ _ ?_)
    have h1 := congrArg (B₀.σ ((IntermediateField.fixingSubgroupEquiv K).symm σ)) hna
    rw [map_mul, map_pow, hg, hsc, hsc] at h1
    rw [map_mul, map_mul, map_pow, map_pow, ← h1, ← hna]
    ring
  obtain ⟨k, hk, hky⟩ := ACris.bCris_fixed_mem_maxUnramified hE hZ (K := K) _ hy
  obtain ⟨e, he⟩ : ∃ e : ℕ, ‖(l : PadicAlgCl l) ^ e * k‖ ≤ 1 := by
    have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := norm_natCast_p_algCl_lt_one
    obtain ⟨e, he⟩ := exists_pow_lt_of_lt_one (show 0 < (‖k‖ + 1)⁻¹ by positivity) hl1
    refine ⟨e, ?_⟩
    rw [norm_mul, norm_pow]
    have h1 : 0 < ‖k‖ + 1 := by positivity
    calc ‖(l : PadicAlgCl l)‖ ^ e * ‖k‖ ≤ (‖k‖ + 1)⁻¹ * (‖k‖ + 1) :=
          mul_le_mul he.le (by linarith) (norm_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ h1.ne'
  obtain ⟨w, hw⟩ := hK r (mul_mem (pow_mem (natCast_mem _ l) e) hk) he
  refine ⟨e, w, ?_⟩
  have hA : (l : Acris l) ^ e * a = tA l ^ n * r.w w :=
    iC_inj (pullback_fin_relation (fB l) (ACris.iotaB hE hZ) (DeRhamPotentiallySemistable.DRPst.iC l)
      ((algebraMap (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l)).comp (algClToBdR l : PadicAlgCl l →+* BDeRhamPlus (normInteger ℂ_[l]) l))
      iB_fB hT1 hky hw)
  exact fin2 B₀.c (B₀.t_unit.pow n) hna hA

end UpperTheory.Ru.crystallineComparison.PBI

theorem UpperTheory.Ru.crystallineComparison.pbInv :
    ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (B₀ : PB l K) (r : Res l K), InvC B₀ r :=
  fun _ _ _ _ B₀ r => UpperTheory.Ru.crystallineComparison.PBI.mainC B₀ r
end
end

section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

private theorem UpperTheory.Ru.crystallineComparison.quasiCompact_of_proj {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : QuasiCompact f := by
  refine Exists.elim h fun N hN => Exists.elim hN fun i hi => ?_
  have : IsProper (ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  have : IsClosedImmersion i := hi.1
  rw [← hi.2]
  infer_instance

theorem UpperTheory.Ru.crystallineComparison.final :
    UpperTheory.Ru.crystallineComparison.Final := by
  unfold UpperTheory.Ru.crystallineComparison.Final
  intro l _ K _ _ _ r f hf hx hC ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨Amp, N, F, hFacts, hEt, hLaws, ⟨bm⟩, ⟨pm⟩, hfN, hTeich, hall⟩ := hC
  refine Exists.elim (CrystallineSemistableComparison.E.etMap l K) fun e he => ?_
  refine Exists.elim (UpperTheory.Ru.crystallineComparison.ePin l K Model.Sm Amp e he) fun e' hcomp => ?_
  refine Exists.elim (UpperTheory.Ru.crystallineComparison.pbIota l K B₀) fun ι hι' => ?_
  have hInj : InjE B₀ e M j :=
    UpperTheory.Ru.crystallineComparison.injOf l K B₀ ι hι'.1 hι'.2.1 hι'.2.2.1 Model.Sm Amp hFacts hEt hLaws e e' bm pm hcomp M hM j
  have hAbs : AbsInv B₀ e M j f ϖ :=
    UpperTheory.Ru.crystallineComparison.absInvOf l K r B₀ (UpperTheory.Ru.crystallineComparison.pbInv l K B₀ r) e he M hM f N j hx hfN hTeich F
      (hall M hM j).1 (hall M hM j).2 ϖ hϖ.not_isUnit
  have hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.p := hM.1.1
  have hSm : Smooth M.p := hM.2
  have hQC : QuasiCompact M.p := UpperTheory.Ru.crystallineComparison.quasiCompact_of_proj hP
  have hAff : UpperTheory.Gal.crystallineComparison.AffFin M.X := UpperTheory.Gal.crystallineComparison.affFin_of (OK l K) M.X M.p hP
  exact UpperTheory.Ru.crystallineComparison.top l K ϖ hϖ e he M hSm hQC hAff f n j hf T hr hPt A hA B₀ hInj hAbs
end

section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.finAll_of :
    (∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K) (f : ℕ), 0 < f → CIn l K r f) → UpperTheory.Gal.crystallineComparison.Br.FinAll := by
  intro h l _ K _ _ _ f hf hc ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨r⟩ := UpperTheory.Gal.CD.resEx l K
  have hx : ∀ x : r.k, x ^ l ^ f = x := by
    have hker : RingHom.ker r.ρ = IsLocalRing.maximalIdeal (OK l K) := by
      have hm : (RingHom.ker r.ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective r.ρ r.surj
      exact IsLocalRing.eq_maximalIdeal hm
    have e : IsLocalRing.ResidueField (OK l K) ≃+* r.k :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective r.surj)
    have hcard : Nat.card r.k = l ^ f := by
      rw [← Nat.card_congr e.toEquiv]
      exact hc
    have hfin : Finite r.k :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    have := Fintype.ofFinite r.k
    intro x
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  exact UpperTheory.Ru.crystallineComparison.final l K r f hf hx (h l K r f hf) ϖ hϖ M hM n j T hr hPt A hA B₀
end
