import Formalism.LocalToGlobal.CharacterGerms.ChartHypothesisOfCharacters
import Formalism.LocalToGlobal.CharacterGerms.RowTiePFBMapSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def UPCharSt (Y : FBChart C V O dd) (p : PairData Y d I) (Hc : ∀ g, (Y.raw p).CartHyp V g) : Prop :=
  ∃ (h : Fin 2 → ℕ) (χ : ∀ g, Fin (h g) → PS C 1 dd), (∀ g i, Y.IsChar (χ g i)) ∧
    ∀ g a, p.big g a →
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I g // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        ((Y.raw p).AltC →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' (gam V.l) : ℝ) : WithTop ℝ)) ∧
        ((∀ b, p.big g b) →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' 0 : ℝ) : WithTop ℝ))


section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def UpperCharacterCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), UPCharSt Y (pairOfLab ha hg o) Hc

end Chart

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

section Series

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ}
variable {R : Type} [CommRing R] [Algebra R C]

abbrev toC {n : ℕ} (f : PS R n dd) : PS C n dd := MvPowerSeries.map (algebraMap R C) f

theorem mpt_pt {n : ℕ} (j : Fin n) : MapFB.mpt (algebraMap R C) (pt R dd j) = pt C dd j := by
  funext i
  simp [MapFB.mpt, pt]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt R dd j i) = 0 := by
  simp [pt]

theorem isChar_of_isCh (Y : FBChart C V OE dd) (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) {u : PS R 1 dd} (hu : IsCh FR u) :
    Y.IsChar (toC u) := by
  refine ⟨fun μ => ?_, ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]; exact hR _
  · rw [MvPowerSeries.constantCoeff_map, hu.1, map_one]
  · have h := congrArg (MvPowerSeries.map (algebraMap R C)) hu.2
    have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1) i) = 0 := by
      intro i
      refine MapFB.cc_ev _ ?_ _ (hF0 i)
      intro j i'
      fin_cases j <;> simp [pt]
    rw [map_mul, MapFB.map_ev1 _ _ hadd, MapFB.map_ev1 _ _ (cc_pt 0), MapFB.map_ev1 _ _ (cc_pt 1), mpt_pt, mpt_pt] at h
    have e : MapFB.mpt (algebraMap R C) (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1)) =
        addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) := by
      funext i
      show MvPowerSeries.map (algebraMap R C) (ev ![pt R (n := 2) dd 0, pt R (n := 2) dd 1] (FR i)) = _
      rw [MapFB.map_ev2 _ _ _ (cc_pt 0) (cc_pt 1), mpt_pt, mpt_pt]
      show _ = ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F i)
      rw [hF i]
    rw [e] at h
    exact h


end Series

section Len

theorem lenCoker_mono {R : Type} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h h' : ℕ}
    (B : Matrix (Fin m) (Fin h') R) (f : Fin h → Fin h') :
    S4.lenCoker v B ≤ S4.lenCoker v (B.submatrix id f) := by
  unfold S4.lenCoker
  refine Finset.le_inf fun g _ => ?_
  exact Finset.inf_le (f := fun g : Fin m → Fin h' => v (B.submatrix id g).det) (Finset.mem_univ (f ∘ g))

variable {C : Type} [Field C] {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] {dd : ℕ}

theorem lenCoker_le_of_hasLen (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {s N : ℕ} (W : Fin s → Fin dd → R) (u : Fin N → PS R 1 dd) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen vm R
      ((Fin s → R) ⧸ Submodule.span R (Set.range fun k => res W (dl (u k)))) x)
    {S : ℝ} (hS : vm (V.l : C) ^ S ≤ x) :
    S4.lenCoker V.v (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) ≤
      ((S : ℝ) : WithTop ℝ) := by
  set α : Matrix (Fin s) (Fin N) R := Matrix.of fun c k => res W (dl (u k)) c with hα
  have hr : LinearMap.range α.mulVecLin = Submodule.span R (Set.range fun k => res W (dl (u k))) := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [← hr] at hx
  have hSr : (vm (V.l : C) : ℝ) ^ S ≤ (x : ℝ) := by exact_mod_cast hS
  have hpos : 0 < (x : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 S) hSr
  have e := lenCoker_eq_logb hT hv h0 h1 α hx hpos
  have e2 : (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) =
      Matrix.of fun c k => algebraMap R C (α c k) := by
    ext c k
    simp only [Matrix.of_apply, hα, res, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e2, e]
  refine WithTop.coe_le_coe.mpr ?_
  have h2 : Real.logb (vm (V.l : C) : ℝ) x ≤ Real.logb (vm (V.l : C) : ℝ) ((vm (V.l : C) : ℝ) ^ S) :=
    (Real.logb_le_logb_of_base_lt_one h0 h1 hpos (Real.rpow_pos_of_pos h0 S)).mpr hSr
  rwa [Real.logb_rpow h0 (ne_of_lt h1)] at h2

end Len

section Sum

theorem frobSum_conj_alt {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (q : ZMod d → ℕ)
    (hqb : ∀ b, big b → q b = j') (hqs : ∀ b, ¬ big b → q b = n + j) (a : ZMod d) (ha : big a) :
    S4.frobSum l q a = upB l (n + j) j' (gam l) := by
  rw [S4.frobSum_alt hl j' 0 (n + j) big halt q (fun b hb => by rw [hqb b hb]; rfl) hqs a ha]
  have h1 := S4.one_div_eq_gam_add_rho hl
  have hg : gam l = S4.gam l := rfl
  have hdiv : (j' : ℝ) / ((l : ℝ) - 1) = j' * (S4.gam l + S4.rho l) := by rw [← h1]; ring
  unfold upB
  rw [hg, hdiv]
  push_cast
  ring

theorem frobSum_conj_all {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (q : ZMod d → ℕ) (hq : ∀ b, q b = j')
    (a : ZMod d) : S4.frobSum l q a = upB l (n + j) j' 0 := by
  rw [S4.frobSum_const hl j' q hq a]
  unfold upB
  ring

end Sum

section Core

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def rk {Y : FBChart C V OE dd} (p : PairData Y d I) (g : Fin 2) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => p.ty g c = b).card

def AFBound (Y : FBChart C V OE dd) (p : PairData Y d I) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (FR : Fin dd → PS R 2 dd) : Prop :=
  ∀ g a, p.big g a → ∃ (s : ℕ) (e : Fin s ≃ {x : I g // p.ty g x = a}) (W : Fin s → Fin dd → R) (xs : NNReal),
    (∀ c i, algebraMap R C (W c i) = p.u g (e c) i) ∧ HasAF vm FR W xs ∧
      vm (V.l : C) ^ (S4.frobSum V.l (rk p (1 - g)) a) ≤ xs

theorem upChar_of_afBound (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) (h : AFBound Y p vm R FR) : UPCharSt Y p Hc := by
  have hR : ∀ x : R, V.Ge 0 (algebraMap R C x) := fun x => vA_nonneg hT hv h0 h1 x
  have hl1 : 1 < V.l := V.l_prime.one_lt
  have key : ∀ g a, ∃ (N : ℕ) (u : Fin N → PS C 1 dd), (∀ k, Y.IsChar (u k)) ∧ (p.big g a →
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I g // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        S4.lenCoker V.v (Matrix.of fun c k => p.yOf g (u k) (e c)) ≤
          ((S4.frobSum V.l (rk p (1 - g)) a : ℝ) : WithTop ℝ)) := by
    intro g a
    by_cases hb : p.big g a
    · obtain ⟨s, e, W, xs, hW, ⟨N, u, hu, hx⟩, hS⟩ := h g a hb
      have hs : s = pT (fun g => RawChart.cart (Hc g)) g a := by
        have := Fintype.card_congr e
        rw [Fintype.card_fin, Fintype.card_subtype] at this
        exact this
      subst hs
      refine ⟨N, fun k => toC (u k), fun k => isChar_of_isCh Y hR FR hF hF0 (hu k), fun _ => ⟨e, ?_⟩⟩
      have := lenCoker_le_of_hasLen hT hv h0 h1 W u hx hS
      simp only [hW] at this
      exact this
    · exact ⟨0, fun k => k.elim0, fun k => k.elim0, fun hb' => absurd hb' hb⟩
  choose N u hu he using key
  let eq : ∀ g, (Σ a : ZMod d, Fin (N g a)) ≃ Fin (Fintype.card (Σ a : ZMod d, Fin (N g a))) := fun g => Fintype.equivFin _
  refine ⟨fun g => Fintype.card (Σ a : ZMod d, Fin (N g a)),
    fun g i => u g ((eq g).symm i).1 ((eq g).symm i).2, fun g i => hu g _ _, fun g a hb => ?_⟩
  obtain ⟨e, hle⟩ := he g a hb
  have hle' : S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e c)) ≤
      ((S4.frobSum V.l (rk p (1 - g)) a : ℝ) : WithTop ℝ) := by
    refine le_trans (lenCoker_mono V.v _ (fun k : Fin (N g a) => eq g ⟨a, k⟩)) ?_
    have e3 : (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e c)).submatrix id
        (fun k : Fin (N g a) => eq g ⟨a, k⟩) = Matrix.of fun c k => p.yOf g (u g a k) (e c) := by
      ext c k
      simp only [Matrix.submatrix_apply, Matrix.of_apply, id]
      rw [Equiv.symm_apply_apply]
    rw [e3]
    exact hle
  have hc1 : ∀ b, p.big g b → rk p (1 - g) b = p.j' := fun b hb' =>
    hr.rk_small (1 - g) b (fun hh => (hr.big_compl g b).mp hh hb')
  have hc2 : ∀ b, ¬ p.big g b → rk p (1 - g) b = p.n + p.j := fun b hb' =>
    hr.rk_big (1 - g) b ((hr.big_compl g b).mpr hb')
  refine ⟨e, fun hA => ?_, fun hB => ?_⟩
  · rw [← frobSum_conj_alt hl1 p.n p.j p.j' (p.big g) (alt_step p.big hr.big_compl hA g) (rk p (1 - g)) hc1 hc2 a hb]
    exact hle'
  · rw [← frobSum_conj_all hl1 p.n p.j p.j' (rk p (1 - g)) (fun b => hc1 b (hB b)) a]
    exact hle'

end Core

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def GeoJ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (OE : Type) [CommRing OE] [StarRing OE] (aG : OE → (G ⟶ G)) (dd : ℕ) (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∃ (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
    (U : Out.UnifPre (maximalIdeal T) D A G) (F : FGLaw T dd)
    (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin dd) m) ⟶ G) (_ : Module OE D.toPre.X) (io : Out.RingAct G OE)
    (oD : D.OAct OE) (oA : A.OAct OE) (act : Germ.OAct OE F),
    F.F = FT ∧ act.act = actT ∧ (∀ a, io.act a = aG a) ∧ IsChartJ G F x ∧ U.OLinear OE oD oA io ∧
      ChartActs G x io act

def PlaceIn (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ (w : PlaceU l OE) (_ : NeZero w.n) (t : Fin w.n ≃ Emb (O := R) w.e) (jj : ZMod d ≃ Fin w.n),
    (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : Emb (O := R) w.e) : OE →+* R) = em a) ∧
    ∃ b : Module.Basis (Fin w.n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := R) w.e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def UpFLaw (p : ℕ) [Fact p.Prime] (T : Type) [CommRing T] (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ)
    (FT : Fin dd → PS T 2 dd) (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O]
      [Algebra ℤ_[p] O] (iota : T →+* O), IsLocalHom iota →
    ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e),
    (∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)))) →
    (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a -
        (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ maximalIdeal O) →
    ∀ (r : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (r τ) → Fin dd → O),
      (∀ τ, IsEigBasis (fun a i => MvPowerSeries.map iota (actT a i)) τ (W τ)) →
    ∀ j : Fin w.n, ∃ xs : NNReal,
      HasAF v (fun i => MvPowerSeries.map iota (FT i)) (W ((t j : Emb (O := O) w.e) : OE →+* O)) xs ∧
      v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) *
        (r (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp
          ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs

theorem upFLaw_of_geoJ {p : ℕ} [Fact p.Prime] (hUp : UpFSt p) (hp2 : p ≠ 2)
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T] (hlT : ¬ IsUnit (p : T))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    {OE : Type} [CommRing OE] [StarRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (aG : OE → (G ⟶ G)) {dd : ℕ} (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hG : GeoJ T G OE aG dd FT actT)
    (hdisc : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) : UpFLaw p T OE dd FT actT := by
  obtain ⟨D, A, U, F, x, iM, io, oD, oA, act, rfl, rfl, -, hx, hO, hA⟩ := hG
  intro C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hbas hfrob r W hW j
  exact hUp T hlT G D A U dd F x hx hp2 OE io oD oA hO hdisc act hA C v O hv iota hloc w t hbas hfrob r W hW j

section Inst

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def EigIn {Y : FBChart C V OE dd} (p : PairData Y d I) (R : Type) [CommRing R] [Algebra R C]
    (actR : OE → Fin dd → PS R 1 dd) (emR : Fin 2 → ZMod d → OE →+* R) : Prop :=
  ∃ (r : (OE →+* R) → ℕ) (W : ∀ τ : OE →+* R, Fin (r τ) → Fin dd → R), (∀ τ, IsEigBasis actR τ (W τ)) ∧
    ∀ g a, ∃ e : Fin (r (emR g a)) ≃ {x : I g // p.ty g x = a},
      ∀ c i, algebraMap R C (W (emR g a) c i) = p.u g (e c) i

theorem ofNat_succ (n : ℕ) [NeZero n] (k : ℕ) : Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
  apply Fin.ext
  simp [Fin.ofNat, Fin.val_add, Nat.add_mod]

theorem jj_add {n : ℕ} [NeZero n] (jj : ZMod d ≃ Fin n) (h : ∀ a, jj (a + 1) = jj a + 1) (a : ZMod d) :
    ∀ k : ℕ, jj (a + (k : ZMod d)) = jj a + Fin.ofNat n k
  | 0 => by
    have : Fin.ofNat n 0 = 0 := by apply Fin.ext; simp [Fin.ofNat]
    simp [this]
  | k + 1 => by
    have e : a + ((k + 1 : ℕ) : ZMod d) = (a + (k : ZMod d)) + 1 := by push_cast; ring
    rw [e, h, jj_add jj h a k, ofNat_succ, add_assoc]

theorem afBound_of_upFLaw (Y : FBChart C V OE dd) (p : PairData Y d I)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : vm.Integers R)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x)
    (hPl : ∀ g, PlaceIn V.l OE R d (emR g))
    (hEig : EigIn p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) :
    AFBound Y p vm R (fun i => MvPowerSeries.map iota (FT i)) := by
  have := Y.algClosed
  intro g a _
  obtain ⟨w, iN, t, jj, hj1, hjt, hbas⟩ := hPl g
  obtain ⟨r, W, hW, hWe⟩ := hEig
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hfrob : ∀ (j : Fin w.n) (x : OE), ((t (j + 1) : Emb (O := R) w.e) : OE →+* R) x -
      (((t j : Emb (O := R) w.e) : OE →+* R) x) ^ V.l ∈ maximalIdeal R := by
    intro j x
    obtain ⟨a', rfl⟩ := jj.surjective j
    rw [← hj1, hjt, hjt]
    apply hMM
    rw [map_sub, map_pow, hem, hem]
    exact p.em_frob g a' x
  obtain ⟨xs, hAF, hle⟩ := hL C vm R hv iota hloc w t hbas hfrob r W hW (jj a)
  obtain ⟨e, he⟩ := hWe g a
  have hconj : ∀ b, (emR g b).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom = emR (1 - g) b := by
    intro b
    ext x
    apply hinj
    show algebraMap R C (emR g b (star x)) = _
    rw [hem, hem]
    fin_cases g
    · exact (p.em_conj b x).symm
    · show p.em 1 b (star x) = p.em 0 b x
      rw [p.em_conj, star_star]
  have hrk : ∀ b, r (emR (1 - g) b) = rk p (1 - g) b := by
    intro b
    obtain ⟨e', -⟩ := hWe (1 - g) b
    have := Fintype.card_congr e'
    rw [Fintype.card_fin, Fintype.card_subtype] at this
    exact this
  refine ⟨r (emR g a), e, W (emR g a), xs, he, ?_, ?_⟩
  · rw [hjt a] at hAF
    exact hAF
  · have hs : S4.frobSum V.l (rk p (1 - g)) a = ∑' n : ℕ, ((V.l : ℝ) ^ (-((n : ℝ) + 1))) *
          (r (((t (jj a + Fin.ofNat w.n (n + 1)) : Emb (O := R) w.e) : OE →+* R).comp
            ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ) := by
      unfold S4.frobSum
      refine tsum_congr fun n => ?_
      rw [← jj_add jj hj1 a (n + 1), hjt, hconj, hrk, rpow_neg_succ V.l_prime.pos]
    rw [hs]
    rw [map_natCast] at hle
    exact hle

theorem upChar_of_upFLaw (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hT : ValTie V vm) (hv : vm.Integers R)
    (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (hF : ∀ i, Y.B.G.F i = toC (MvPowerSeries.map iota (FT i)))
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x)
    (hPl : ∀ g, PlaceIn V.l OE R d (emR g))
    (hEig : EigIn p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) : UPCharSt Y p Hc := by
  refine upChar_of_afBound Y p hr Hc vm R hT hv h0 h1 (fun i => MvPowerSeries.map iota (FT i)) hF ?_
    (afBound_of_upFLaw Y p vm R hv hMM T FT actT hL iota hloc emR hem hPl hEig)
  intro i
  apply hv.hom_inj
  have := Y.B.G.const i
  rw [hF i, MvPowerSeries.constantCoeff_map] at this
  rw [this, map_zero]


end Inst

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ValuationFitting

structure RingPk {C : Type} [Field C] (V : VF C) where
  vm : Valuation C NNReal
  tie : ValTie V vm
  int : vm.Integers V.RR
  pos : 0 < (vm (V.l : C) : ℝ)
  lt : (vm (V.l : C) : ℝ) < 1
  nonunit : ¬ IsUnit ((V.l : ℕ) : V.RR)
  cpl : IsAdicComplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR
  loc : IsLocalRing V.RR
  alg : Algebra ℤ_[V.l] V.RR
  mm : ∀ x : V.RR, V.MM (x : C) → x ∈ IsLocalRing.maximalIdeal V.RR

def RingPkSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → Nonempty (RingPk V)

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end
