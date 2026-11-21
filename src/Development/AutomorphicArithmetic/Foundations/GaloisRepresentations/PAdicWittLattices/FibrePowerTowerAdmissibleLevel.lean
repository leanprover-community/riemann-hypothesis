import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PNuInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSysOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGSimOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresChangeOfForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateTwist
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFullOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelArith
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransSelf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHomPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOfMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PQuotUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransUniqPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPowSm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.GObjMapCast
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtOrbit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitForget
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PDescMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHomDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjective
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitFree
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwFEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSigmaFEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSumFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMemOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.ExistsDeeperNormalLevel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasicHolds

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem dvd_of_mult {p : ℕ} [Fact p.Prime] {m n : ℕ} (hm : m.Coprime p) {s t t' : AfP p}
    (hs : IsIntAf s) (ht' : IsIntAf t') (e : t * t' = 1) (h : (n : AfP p) * t = (m : AfP p) * s) : m ∣ n := by
  have hpos : 0 < m := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hm)
  refine Int.natCast_dvd_natCast.1 (GlobalTheory.IntDvdAdele.dvd_of_eq_mul_int p m hpos hm (n : ℤ) (s * t')
    (GlobalTheory.HeckeApprox.isInt_mul hs ht') ?_)
  rw [Int.cast_natCast, ← _root_.mul_assoc, ← h, _root_.mul_assoc, e, _root_.mul_one]

theorem UpperTheory.Gal.G3.pMultBasic :
    NuInt → MultBasic := by
  intro hNu p _
  refine ⟨?_, ?_, ?_⟩
  · rintro a c c' hc hc' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    have h : (c : AfP p) * t = (c' : AfP p) * s := ha.symm.trans ha'
    exact Nat.dvd_antisymm (dvd_of_mult hc ht hs' e' h.symm) (dvd_of_mult hc' hs ht' e h)
  · rintro a a' c c' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    refine ⟨t * s, t' * s', GlobalTheory.HeckeApprox.isInt_mul ht hs, GlobalTheory.HeckeApprox.isInt_mul ht' hs', ?_, ?_⟩
    · rw [_root_.mul_mul_mul_comm, e, e', _root_.one_mul]
    · rw [ha, ha', Nat.cast_mul, _root_.mul_mul_mul_comm]
  · intro D G L u hu
    refine ⟨UpperTheory.Gal.G3.mul u, UpperTheory.Gal.G3.mul u⁻¹, hNu p D G L u (UpperTheory.Gal.Int.Geo.integ_of_mem hu),
      hNu p D G L u⁻¹ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hu)),
      Units.mul_inv ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2), ?_⟩
    rw [Nat.cast_one, _root_.one_mul]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

private theorem conj_core {V : Type*} [AddCommGroup V] [Module ℚ V] (H U Hi : V →+ V) {k N : ℕ} (hk : 0 < k) {v w : V}
    (hv : H (Hi v) = v) (e : U (k • Hi v) = k • Hi v + (N * k) • w) : H (U (Hi v)) = v + N • H w := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h1 := congrArg H e
  simp only [map_nsmul, map_add, hv] at h1
  have h2 : k • H (U (Hi v)) = k • (v + N • H w) := by
    rw [h1, smul_add, mul_comm N k, mul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ k, ← Nat.cast_smul_eq_nsmul ℚ k] at h2
  exact MulAction.injective₀ hk' h2

private theorem congOne_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {h u : G.GAf} {k N : ℕ}
    (hI : Integ L h) (hk : 0 < k) (hinv : ∀ v ∈ LaHat D, k • L.actG h⁻¹ v ∈ LaHat D) (hu : L.CongOne (N * k) u) :
    L.CongOne N (h * u * h⁻¹) := by
  intro v hv
  obtain ⟨w, hw, e⟩ := hu _ (hinv v hv)
  refine ⟨L.actG h w, hI w hw, ?_⟩
  have hhv : L.actG h (L.actG h⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := conj_core (L.actG h).toAddMonoidHom (L.actG u).toAddMonoidHom (L.actG h⁻¹).toAddMonoidHom hk (v := v) (w := w) hhv e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  exact this

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pAdmOf :
    AdmOf := by
  intro p _ D G L h k N hI hk hinv u hu
  refine ⟨congOne_conj L hI hk hinv hu.1, ?_⟩
  have e : (h * u * h⁻¹)⁻¹ = h * u⁻¹ * h⁻¹ := by group
  rw [e]
  exact congOne_conj L hI hk hinv hu.2
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pKNCong :
    KNCong := by
  intro p _ D G L N _ _ u hu h
  have h1 : L.CongOne N u := GlobalTheory.AdelicSim.congOne_of D (L.actG u) N h
  refine ⟨h1, ?_⟩
  intro v hv
  obtain ⟨w₁, hw₁, e₁⟩ := hu.2 v hv
  have hv' : L.actG u⁻¹ v ∈ LaHat D := by
    rw [e₁]
    exact add_mem hv (nsmul_mem hw₁ _)
  obtain ⟨w, hw, e⟩ := h1 _ hv'
  have e' : L.actG u (L.actG u⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ⟨-w, neg_mem hw, ?_⟩
  rw [e'] at e
  rw [smul_neg]
  exact eq_add_neg_of_add_eq e.symm
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTateDiff :
    TateDiff := by
  intro p _ D G L R _ _ gb S s N o k _ _ t I J hI hJ
  have hN : 0 < N.1 := by have := N.2.1; omega
  have hNp : N.1.Coprime p := N.2.2
  obtain ⟨g, hg⟩ := GlobalTheory.LKGeo.GammaUniq.exists_simSys_all hN hNp
    (fun n q q' z z' h h' => GlobalTheory.weilIs_unique_fieldPoint S o.A _ (LB.isLB_pull o.isLB _) k t n q q' z z' h h')
    (GenCmp.tateRestrict J) (GenCmp.tateRestrict I)
    (fun y => (hJ y).symm.trans (hI y))
  obtain ⟨u, hu, hh⟩ := GlobalTheory.T.similitude_action_adelic_lattice p D G L N.1 hN hNp g
  refine ⟨u, hu, fun n hn hc x y => ?_⟩
  have e₁ : I.ev n x = J.ev n (g.g n x) := hg n hn hc x
  have e₂ : ∀ a b : D.La, J.ev n a = J.ev n b ↔ ∃ z, a = b + n • z := fun a b =>
    GlobalTheory.UPel.HT.TateCompare.ev_eq_iff (GenCmp.tateRestrict J) hn hc
  obtain ⟨w, hw, e₃⟩ := hh n hn hc x
  let f : D.La →+ (AfP p ⊗[ℚ] VQ D) := AddMonoidHom.mk' (inAf D) (GlobalTheory.LKGeo.GammaUniq.inAf_add (p := p) (D := D))
  have hf : ∀ a, f a = inAf D a := fun _ => rfl
  rw [Category.comp_id, e₁, e₂]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨inAf D z + w, add_mem (GlobalTheory.LKGeo.GammaUniq.inAf_mem z) hw, ?_⟩
    rw [e₃, hz, ← hf, ← hf, ← hf, map_add, map_nsmul, smul_add, add_assoc]
  · rintro ⟨v, hv, e₄⟩
    have e₅ : inAf D (g.g n x - y) = n • (v - w) := by
      rw [← hf, map_sub, hf, hf, smul_sub]
      rw [e₃] at e₄
      rw [sub_eq_sub_iff_add_eq_add, e₄, add_comm]
    obtain ⟨z, hz⟩ := GlobalTheory.LKGeo.LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hc _ (sub_mem hv hw) e₅
    exact ⟨z, by rw [← hz]; abel⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTatePull :
    TatePull := by
  intro p _ D R _ _ gb S S' s s' f N o o' m k _ t
  have hT := HeckeRestrict.tate_pullback D.toG o.A o'.A o.act o'.act o.P o'.P o.isLB o'.isLB f m.φ m.φ₂
    m.cart m.sq m.act m.pol k t
  have hpt : ∀ y, (toUnit (Over.mk (t ≫ f)) ≫ o.eta y).left = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left, m.eta y]
    exact Category.assoc _ _ _
  have hpt' : ∀ y, (toUnit (Over.mk t) ≫ o'.eta y).left ≫ m.φ = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left]
    exact Category.assoc _ _ _
  refine ⟨fun I => ?_, fun I' => ?_⟩
  · obtain ⟨I', hI'⟩ := hT.2 I
    refine ⟨I', fun hI y => ?_, fun n x => (hI' n x).symm⟩
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hpt', ← hpt, hI y, hI' N y]
    · rw [Over.w, Over.w]
  · obtain ⟨I, hI⟩ := hT.1 I'
    refine ⟨I, fun hI' y => ?_, fun n x => (hI n x).symm⟩
    apply Over.OverMorphism.ext
    rw [hpt, hI N y, ← hI' y, hpt']
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isUnit_nat_of_rat {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}} (s : S ⟶ Sp R) {d : ℕ}
    (hd : 0 < d) : IsUnit (d : Γ(S, ⊤)) := by
  have hR : IsUnit (d : R) := by
    have hq : IsUnit (algebraMap ℚ R (d : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast hd.ne')).map _
    simpa using hq
  have h := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
  simpa using h

theorem UpperTheory.Gal.G3.pIsogFEt :
    IsogFEt := by
  intro R _ _ S s A A' _ _ _ _ hA hA' ψ ψ' d hd hψ hψ' h1 h2
  exact GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv S A A' d ψ ψ' hA hA'
    (isUnit_nat_of_rat s hd) ⟨hψ, hψ', h1, h2⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pMapOfIso :
    MapOfIso := by
  intro G₀ R _ _ gb S s N o o' θ hiso hmon hact hpol heta
  haveI : IsIso θ.left := (Over.forget S).map_isIso θ
  refine ⟨⟨θ.left, Hecke.sq2 θ, ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, ?_⟩, ⟨?_, ?_⟩,
    fun c => ?_, hpol, fun y => ?_⟩, rfl⟩
  · intro T x y x₀ y₀ hx hy
    let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have ex : x₀ = u ≫ x ≫ θ := Over.OverMorphism.ext (by simp [u, hx])
    have ey : y₀ = u ≫ y ≫ θ := Over.OverMorphism.ext (by simp [u, hy])
    rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
    simp [u]
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  · rw [← Over.comp_left, hact c, Over.comp_left]
  · rw [← Over.comp_left, heta y, Category.id_comp]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransFree :
    KNCong → TransFree := by
  intro hK p _ D G L R _ _ gb k _ _ s N o u hu hT
  obtain ⟨-, -, -, -, hp⟩ := hT
  obtain ⟨I', I'', h', h'', hr⟩ := hp k (𝟙 _) (Spec.preimage (𝟙 _ ≫ s)).hom (by
    simp [spMap])
  refine hK p D G L N.1 (by have := N.2.1; omega) N.2.2 u hu fun x => ?_
  exact (hr N.1 (by have := N.2.1; omega) N.2.2 x x).1 (by
    rw [← h' x, ← h'' x]; simp)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pGenSm : GenSm := by
  intro p _ D R _ _ gb N X
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R (GenCmp.baseOf gb) N.1 N.2.1 N.2.2
  obtain ⟨j, hoi, hci, hj, -⟩ := GenCmp.genModel_eq_genericFibre p D R (GenCmp.baseOf gb) R (RingHom.id R) gb
    rfl (fun _ => rfl) N.1 N.2.1 N.2.2 M X
  haveI := hoi
  haveI := hci
  haveI : IsQProjOver M.s := M.qproj
  haveI : SmoothOfRelativeDimension (D.a * (D.n - 1)) M.s := M.smooth
  haveI : IsSeparated M.s := GlobalTheory.ZM.isSeparated_of_isQProjOver M.qproj
  haveI : QuasiCompact M.s := quasiCompact_of_qProj M.qproj
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  rw [← hj]
  refine ⟨inferInstance, inferInstance, inferInstance, fun hB => ?_⟩
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd (RingHom.id R)
      (Model.isProjOver_of_compactB p D R (GenCmp.baseOf gb) N.1 N.2.1 N.2.2 hB M))
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pEtDesc :
    ExtPts → EtDesc := by
  intro hE W Z Y B _ c _ _ _ pZ pY _ f hf hpts
  haveI : Flat c := inferInstance
  haveI : EffectiveEpi c := inferInstance
  haveI : IsReduced (pullback c c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst c c)
  have key : pullback.fst c c ≫ f = pullback.snd c c ≫ f := by
    refine hE pY _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, ← Category.assoc, pullback.condition]
    · intro Ω _ _ x
      refine hpts Ω (x ≫ pullback.fst c c) (x ≫ pullback.snd c c) ?_ |>.trans ?_ <;> simp [pullback.condition]
  refine ⟨inferInstance, EffectiveEpi.desc c f (fun {T} g₁ g₂ h => ?_), EffectiveEpi.fac _ _ _⟩
  have e₁ : pullback.lift g₁ g₂ h ≫ pullback.fst c c = g₁ := pullback.lift_fst _ _ _
  have e₂ : pullback.lift g₁ g₂ h ≫ pullback.snd c c = g₂ := pullback.lift_snd _ _ _
  calc g₁ ≫ f = pullback.lift g₁ g₂ h ≫ pullback.fst c c ≫ f := by rw [← Category.assoc, e₁]
    _ = pullback.lift g₁ g₂ h ≫ pullback.snd c c ≫ f := by rw [key]
    _ = g₂ ≫ f := by rw [← Category.assoc, e₂]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitCart :
    TransIso → WitCart := by
  intro hI p _ D G L R _ _ gb N' N X' X u hu π Φ hW
  obtain ⟨-, o, ψ, φ, hT, rfl⟩ := hW
  have hψ : IsIso ψ := hI p D G L R gb X'.X X'.s N' N X'.univ o ψ u hu hT
  have hl : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget _).map ψ))
  have h₁ : IsPullback ψ.left X'.univ.A.hom o.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz φ.cart.1
  rwa [Category.id_comp] at h₂
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitDeep :
    KNBasic → GenSm → TransDeep → WitComp → WitForget → WitDeep := by
  intro _ hSm hTD hWC hWF p _ D G L R _ _ gb X N' N h hI
  obtain ⟨k, hk, hAk, hex⟩ := hTD p D G L R gb h hI
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left _ |>.mp hk) (Fact.out : p.Prime).one_lt.ne'
    · exact hpos
  let Nk : Lv p := ⟨↑N * k, le_trans N.2.1 (Nat.le_mul_of_pos_right _ hk0), Nat.Coprime.mul N.2.2 hk⟩
  let M : Lv p := ⟨↑N' * (↑N * k), le_trans Nk.2.1 (Nat.le_mul_of_pos_left _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul N'.2.2 Nk.2.2⟩
  have hNkM : (↑Nk : ℕ) ∣ ↑M := Dvd.intro_left _ rfl
  refine ⟨M, Dvd.intro _ rfl, ?_, ?_⟩
  · intro u hu
    exact hAk N u (UpperTheory.Gal.Int.Geo.KN_anti hNkM hu)
  · haveI : Smooth (X Nk).s := (hSm p D R gb Nk (X Nk)).1
    haveI : IsLocallyNoetherian (X Nk).X := LocallyOfFiniteType.isLocallyNoetherian (X Nk).s
    obtain ⟨o, ψ, ht⟩ := hex N (X Nk).X (X Nk).s (X Nk).univ
    obtain ⟨π, ⟨hπ, ⟨φ⟩⟩, -⟩ := (X N).rep (X Nk).X (X Nk).s o
    have w₂ : Wit L h (X Nk) (X N) π (ψ.left ≫ φ.φ) := ⟨hπ, o, ψ, φ, ht, rfl⟩
    obtain ⟨c, Φc, w₁, -⟩ := hWF p D G L R gb Nk M hNkM (X Nk) (X M)
    have := (hWC p D G L R gb M Nk N (X M) (X Nk) (X N) 1 h).2 hI (hAk N) c Φc π _ w₁ w₂
    rw [_root_.mul_one] at this
    exact ⟨_, _, this⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitOne :
    GenSm → WitUniq → WitComp → WitForget → WitOne := by
  intro hS hU hC hF p _ D G L R _ _ gb X N' N hA π Φ hW
  let M : Lv p := ⟨N.1 * N'.1, Nat.le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N.2.2 N'.2.2⟩
  have hI : Integ L (1 : G.GAf) := fun v hv => by simpa using hv
  have hMN : AdmK L M.1 N.1 1 := fun u hu => by
    simpa using UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro _ rfl : N.1 ∣ M.1) hu
  obtain ⟨c, Φc, Wc, cF, cE, cS⟩ := hF p D G L R gb N' M (Dvd.intro_left _ rfl) (X N') (X M)
  obtain ⟨e, Φe, We, eF, eE, eS⟩ := hF p D G L R gb N M (Dvd.intro _ rfl) (X N) (X M)
  have W1 := (hC p D G L R gb M N' N (X M) (X N') (X N) 1 1).2 hI hA c Φc π Φ Wc hW
  rw [_root_.mul_one] at W1
  have hce : c ≫ π = e := (hU p D G L R gb M N (X M) (X N) 1 hI hMN _ _ _ _ W1 We).1
  obtain ⟨s1, s2, s3, -⟩ := hS p D R gb N' (X N')
  obtain ⟨t1, t2, t3, -⟩ := hS p D R gb N (X N)
  have hs : π ≫ (X N).s = (X N').s := hW.1
  have sep : IsSeparated (π ≫ (X N).s) := by rw [hs]; exact s2
  have lft : LocallyOfFiniteType (π ≫ (X N).s) := by rw [hs]; infer_instance
  have πS : IsSeparated π := IsSeparated.of_comp π (X N).s
  have πL : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π (X N).s
  have hE : Etale (c ≫ π) := by rw [hce]; exact eE
  have hFi : IsFinite (c ≫ π) := by rw [hce]; exact eF
  obtain ⟨r1, r2⟩ := GlobalTheory.etale_isFinite_of_comp_etale_surjective _ _ _ c π cE cS hE hFi πS πL
  have hSu : Surjective (c ≫ π) := by rw [hce]; exact eS
  exact ⟨r2, r1, Surjective.of_comp c π⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitTrans :
    KNBasic → PtEq → PtOrbit → WitComp → WitTrans := by
  intro hKN hEq hOrb hWC p _ D G L R _ _ gb X N' N π Φ hW k _ _ x y hxy
  obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθΦ⟩ := hOrb p D G L R gb N' N (X N') (X N) π Φ hW k x y hxy
  refine ⟨u, hu, fun π' Φ' hW' => ?_⟩
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have h1 : (1 : G.GAf) ∈ L.KN 1 := one_mem _
  have hid := (hWC p D G L R gb N' N' N' (X N') (X N') (X N') 1 1).1 1 (one_mem _)
  obtain ⟨hA, hB⟩ := hEq p D G L R gb N' N' N' (X N') (X N') (X N') u 1 u 1 π' Φ' (𝟙 _) (𝟙 _) hW' hid
    (UpperTheory.Gal.Int.Geo.integ_of_mem hu1) (UpperTheory.Gal.Int.Geo.integ_of_mem h1)
    ((hKN p D G L N').1 u hu1) ((hKN p D G L N').1 1 h1) (one_mem _) (by simp) k (x ≫ (X N').s) x y rfl hys
    ox oy mx my θ hθ
  refine ⟨by simpa using hA, fun a ha => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ mx.φ = a :=
    ⟨_, mx.cart.1.lift_fst a (𝟙 _) (by rw [ha, Category.id_comp])⟩
  simp only [Category.assoc]
  rw [reassoc_of% hB, hθΦ]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pKSNice :
    KNBasic → PowSm → TwFEt → SigmaFEt → KSNice := by
  intro hKN hP hT hS p _ D G L hsc R _ _ gb k T N J g
  have hq := T.e_q N
  obtain ⟨hsm, -, hpr⟩ := hP p D R gb N (T.M N) k
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (T.X.q (T.lev N))
    rw [← hq]
    infer_instance
  · show IsProjOver (T.X.q (T.lev N))
    rw [← hq]
    exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion _ (hpr hsc.cpt)
  · intro j
    dsimp only [UpperTheory.Gal.Int.Geo.KS.tower]
    have hne : ((L.KN ↑N).subgroupOf (g j).K).index ≠ 0 := by
      have h0 := (hKN p D G L 1).2.2 N (by norm_num) (by have := N.2.1; omega)
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ (g j).le (g j).le_one] at h0
      exact left_ne_zero_of_mul h0
    haveI : ((L.KN ↑N).subgroupOf (g j).K).FiniteIndex := ⟨hne⟩
    refine ⟨_, hS _ _ _ (hT T.X _ _ ⟨?_, ?_⟩)⟩
    · exact one_mem _
    · intro u hu
      rw [T.K_eq] at hu ⊢
      simpa using UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd hu
end

section
open UpperTheory.Gal.Int.Geo (KSEx KSNice)

universe u

namespace UpperTheory.Gal.G3

theorem nuInt_holds : NuInt := @pNuInt

theorem multBasic_holds : MultBasic := @pMultBasic @nuInt_holds

theorem kNBasic_holds : KNBasic := @pKNBasic

theorem sysOf_holds : SysOf := @pSysOf @nuInt_holds

theorem fibrePowerTower_admissibleLevel : AdmOf := @pAdmOf

theorem kNCong_holds : KNCong := @pKNCong

theorem gSimOf_holds : GSimOf := @pGSimOf @multBasic_holds

theorem relComp_holds : RelComp := @pRelComp

theorem tateDiff_holds : TateDiff := @pTateDiff

theorem tateTwist_holds : TateTwist := @pTateTwist @gSimOf_holds

theorem fullOf_holds : FullOf := @pFullOf

theorem relArith_holds : RelArith := @pRelArith

theorem transSelf_holds : TransSelf := @pTransSelf @multBasic_holds @relComp_holds @tateTwist_holds

theorem transComp_holds : TransComp := @pTransComp @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds

theorem homPull_holds : HomPull := @pHomPull

theorem tatePull_holds : TatePull := @pTatePull

theorem transPull_holds : TransPull := @pTransPull @homPull_holds @tatePull_holds

theorem transOfMap_holds : TransOfMap := @pTransOfMap @multBasic_holds @relComp_holds @tatePull_holds

theorem rigid_holds : Rigid := @pRigid

theorem isogFEt_holds : IsogFEt := @pIsogFEt

theorem transKer_holds : TransKer := @pTransKer @relComp_holds @tateDiff_holds @tateTwist_holds

theorem polUniq_holds : PolUniq := @pPolUniq

theorem mapOfIso_holds : MapOfIso := @pMapOfIso

theorem transDeep_holds : TransDeep := @pTransDeep @sysOf_holds @fibrePowerTower_admissibleLevel @fullOf_holds @relArith_holds

theorem transIso_holds : TransIso := @pTransIso @isoPts_holds @isogFEt_holds

theorem transOrbit_holds : TransOrbit := @pTransOrbit @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @kNCong_holds @transIso_holds

theorem transFree_holds : TransFree := @pTransFree @kNCong_holds

theorem genSm_holds : GenSm := @pGenSm

theorem powSm_holds : PowSm := @pPowSm @genSm_holds

theorem etDesc_holds : EtDesc := @pEtDesc @extPts_holds

theorem ptOrbit_holds : PtOrbit := @pPtOrbit @transComp_holds @transPull_holds @transOfMap_holds @transOrbit_holds @rigid_holds

theorem witComp_holds : WitComp := @pWitComp @transSelf_holds @transComp_holds @transPull_holds

theorem witCart_holds : WitCart := @pWitCart @transIso_holds

theorem witForget_holds : WitForget := @pWitForget @mapOfIso_holds @transSelf_holds

theorem witDeep_holds : WitDeep := @pWitDeep @kNBasic_holds @genSm_holds @transDeep_holds @witComp_holds @witForget_holds

theorem homDesc_holds : HomDesc := @pHomDesc @etDesc_holds

theorem polDesc_holds : PolDesc := @pPolDesc

theorem transDesc_holds : TransDesc := @pTransDesc @isogFEt_holds @tatePull_holds @homDesc_holds @polDesc_holds

theorem transCancel_holds : TransCancel := @pTransCancel @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @transIso_holds

theorem twFEt_holds : TwFEt := @pTwFEt @fEtBasic_holds @twGal_holds

theorem sigmaFEt_holds : SigmaFEt := @pSigmaFEt




theorem kSNice_holds : KSNice := @pKSNice @kNBasic_holds @powSm_holds @twFEt_holds @sigmaFEt_holds

theorem quotUniq_holds : QuotUniq := @pQuotUniq @etDesc_holds

theorem transUniqPt_holds : TransUniqPt := @pTransUniqPt @multBasic_holds @isogFEt_holds @transKer_holds @quotUniq_holds @polUniq_holds @mapOfIso_holds

theorem ptEq_holds : PtEq := @pPtEq @transSelf_holds @transComp_holds @transPull_holds @transUniqPt_holds @rigid_holds

theorem witUniq_holds : WitUniq := @pWitUniq @genSm_holds @extPts_holds @transSelf_holds @ptEq_holds

theorem descMap_holds : DescMap := @pDescMap @genSm_holds @etDesc_holds @ptEq_holds @ptOrbit_holds @witCart_holds

theorem witEx_holds : WitEx := @pWitEx @kNBasic_holds @genSm_holds @rigid_holds @witForget_holds @witDeep_holds @descMap_holds @transIso_holds @transCancel_holds @transDesc_holds

theorem witOne_holds : WitOne := @pWitOne @genSm_holds @witUniq_holds @witComp_holds @witForget_holds

theorem witTrans_holds : WitTrans := @pWitTrans @kNBasic_holds @ptEq_holds @ptOrbit_holds @witComp_holds

theorem witFree_holds : WitFree := @pWitFree @kNBasic_holds @transComp_holds @transPull_holds @transOfMap_holds @transFree_holds @ptEq_holds @witCart_holds @witEx_holds

theorem kSEx_holds : KSEx := @pKSEx @kNBasic_holds @witUniq_holds @witComp_holds @witCart_holds @witEx_holds @witOne_holds @witTrans_holds @witFree_holds

end UpperTheory.Gal.G3
end
