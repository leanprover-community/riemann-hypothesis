import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumThetaFactorsPlaceByPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumDisjointUnion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumPartialProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DivisiblePontryaginAnnihilatorDuality
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitDatumCompletedLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AtMostOneHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.TopCongr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_invariant {a b : Type} [Fintype a] [DecidableEq a] {f : Matrix a b k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, IntM x → MaxM y → f (x + y) = f x) {g : Matrix a a k} (hg : MaxM (g - 1)) (x : Matrix a b k) :
    f (g * x) = f x := by
  by_cases hx : IntM x
  · have e : g * x = x + (g - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
    rw [e, hp x _ hx (hg.mul_intM hx)]
  · obtain ⟨u, hu, rfl⟩ := exists_mem_KOne hg
    have h1 : f x = 0 := by_contra fun h => hx (hs x h)
    have h2 : f (u.val * x) = 0 := by_contra fun h => hx (by
      have := (mem_KO.1 (KOne_le_KO hu)).2.mul (hs _ h)
      rwa [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this)
    rw [h1, h2]

theorem hat_eq_zero [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem phiTop_eq (z : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2)) (XIx (Fin κ) t (s + 1) ⊕ Fin 0) k) :
    (S.T t).PhiTop z = (S.P.iter t S.μ S.tame (s + 1)).Phi t (S.μ (s + 1 + 1))
      (z.submatrix (ixSucc _ t (s + 1)) (stdOrd (Fin κ) t (s + 1) 0 rfl)) := by
  have e : (typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (s + 1) 0 rfl)).bas = 1 := by
    change embA _ _ = 1
    rw [Subsingleton.elim (SplitFlip.diagGL _) 1, map_one]
  change S.P.iterPhi t S.μ S.tame (s + 1) (LatFrame.coords _ _ z) = _
  unfold LatFrame.coords TypeDatum.iterPhi
  rw [e]
  simp [LatFrame.refl, typeFrame]

theorem symmetricChain_psi_base_eq_one_of_maximalIdeal {d : XIx (Fin κ) t (s + 1) → k} (hd : ∀ i, valuation k (d i) < 1) :
    S.ψ (-1 * (d ⬝ᵥ S.y0 t)) = 1 := by
  refine (S.cond 1).2 (by simp) _ ?_
  have h := (S.unif _).1 (hd (Sum.inl (Sum.inr 0)))
  have h0 : (0 : ValueGroupWithZero k) < valuation k (S.ϖ : k) := by
    rw [zero_lt_iff]; simp
  simp only [SymData.y0, dotProduct_single, neg_mul, one_mul, Valuation.map_neg, map_mul, map_one,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [← div_eq_mul_inv]
  exact (div_le_one₀ h0).2 h

theorem xiTop_mul_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (g : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) k), (∀ r c, valuation k ((g - 1) r c) < 1) → ∀ x : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k, (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) (g * x) = (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) x := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ g hg x
  refine mul_invariant (fun x hx => ?_) (fun x y hx hy => ?_) hg x
  · unfold Chain.xiTop at hx
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rintro (i | i) j
    · rw [phiTop_eq] at h1
      simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ t (s + 1)).symm i)
        ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl j))
    · exact by_contra fun h => h2 (hat_eq_zero S.cond hν (by simp) _ fun h' => h (h' j))
  · unfold Chain.xiTop
    have hxy := hx.add hy.intM
    rw [Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hx _), Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hxy _),
      phiTop_eq, phiTop_eq]
    congr 1
    · have e : fromCols (x + y).toRows₁ (0 : Matrix _ (Fin 0) k) = fromCols x.toRows₁ 0 + fromCols y.toRows₁ 0 := by
        ext i (j | j)
        · rfl
        · exact j.elim0
      rw [e, submatrix_add]
      refine TypeDatum.Phi_add _ (S.tame _) _ fun i j => ?_
      rw [submatrix_apply]
      rcases stdOrd (Fin κ) t (s + 1) 0 rfl j with j | j
      · exact hy _ _
      · exact j.elim0
    · have e : (x + y) (Sum.inr ()) = x (Sum.inr ()) + y (Sum.inr ()) := rfl
      rw [e, add_dotProduct, mul_add, AddChar.map_add_eq_mul, symmetricChain_psi_base_eq_one_of_maximalIdeal S t (hy _), mul_one]

end GlobalTheory.TopCongr
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.StdMatch
open GlobalTheory.LocMod GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

section Gen
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latO_le (S T : HSp D) (LS LT) {p q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, p v → q v) : latO S T LS LT p ≤ latO S T LS LT q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

theorem mem_latO_at (q : GlobalTheory.FinPl.SplitPt D k) {S T : HSp D} {LS LT} {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True)
    (hh : IsHalf q.e u) : u ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, ⟨β, rfl, h1, h0⟩, hsum⟩ := q.above
  have hβ : β ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have main : (latO S T LS LT fun _ => True) ≤ (latO S T LS LT (· = q.v)).comap
      (DistribSMul.toAddMonoidHom (WO S T) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, h0 v hv, zero_mul]
    · ext i j
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Matrix.of_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  have h := main hu
  rw [AddSubgroup.mem_comap] at h
  convert h using 1
  ext i j
  change _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * u i j
  rw [← hsum, ← hh i j, ← mul_assoc, add_mul, q.split.1, mul_comm (cA D q.e), q.split.2.1, add_zero]

theorem int_iff_up_mem (q : GlobalTheory.FinPl.SplitPt D k) (hq : q.UnitAA) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (eS : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (eT : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (hFS : ∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v))
    (hFT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v))
    (x : Matrix Y Y' k) : (∀ r s, x r s ∈ 𝒪[k]) ↔ (ofSplit q).up FS FT x ∈ stdHom S T := by
  rw [stdHom, ← eS, ← eT]
  refine ⟨fun hx => latO_le S T _ _ (fun _ _ => trivial) (GlobalTheory.UpMem.up_mem_latO D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT x hx),
    fun hx => ?_⟩
  have hh := Witness.up_half (ofSplit q) FS FT x
  obtain ⟨x', hx', e⟩ := GlobalTheory.HalfIntUp.exists_int_up D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT _ (mem_latO_at q hx hh) hh
  have := congrArg ((ofSplit q).down FS FT) e
  rw [Witness.down_up, Witness.down_up] at this
  rwa [this]

theorem gamma_int (q : GlobalTheory.FinPl.SplitPt D k) {Y : Type} [Fintype Y] [DecidableEq Y] {T : HSp D} (FT : Frame k T.rank Y)
    {LT : GlobalTheory.FinPl.Lat T} (eT : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (hFT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) (r s) :
    FT.γ r s ∈ 𝒪[k] := by
  refine (hFT fun r => FT.γ r s).2 ?_ r
  have hs : (Pi.single s 1 : Fin T.rank → D.host.E) ∈ LT := by
    rw [← SetLike.mem_coe, eT]
    intro i
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  convert GlobalTheory.UpMem.e_mul_mem_latV q T LT hs using 2 with i
  have : (FT.β *ᵥ fun r => FT.γ r s) i = (FT.β * FT.γ) i s := rfl
  rw [this, FT.βγ, ← q.sec_pr, Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

theorem mk_eq_mk_of_int {n : Type} {x y : n → k} (h : ∀ c, y c - x c ∈ 𝒪[k]) :
    (Submodule.Quotient.mk x : _ ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk y :=
  ((Submodule.Quotient.eq _).2 (show y - x ∈ box n (1 : kˣ) from fun c => h c)).symm

end Gen

section Mat
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k]

theorem mul_toLoc (ι : E →+* k) {Y Y' : Type} [Fintype Y] [Fintype Y'] {a b nS nT : ℕ} (hS : nS = a) (hT : nT = b)
    (f : (Fin a → E) ≃ₗ[E] (Fin a → E)) (f' : (Fin b → E) ≃ₗ[E] (Fin b → E)) (e' : Y' ≃ Fin a) (e : Y ≃ Fin b)
    (β : Matrix (Fin nS) Y' k) (M : Matrix (Fin nT) Y k) (hβ : ∀ r c, β r c = ι (f (Pi.single (e' c) 1) (finCongr hS r)))
    (hM : ∀ r c, M r c = ι (f' (Pi.single (e c) 1) (finCongr hT r))) (γ : Matrix (Fin nT) (Fin nS) E) :
    M * toLoc ι e e' (Formalism.L2.Col.inFr f f' (Matrix.toLin' (γ.reindex (finCongr hT) (finCongr hS)))) = γ.map ι * β := by
  subst hS hT
  ext r c
  have key : ∀ x : Fin nT → E, ∑ y : Y, f' (Pi.single (e y) 1) r * x (e y) = f' x r := fun x => by
    rw [e.sum_comp fun j => f' (Pi.single j 1) r * x j]
    conv_rhs => rw [pi_eq_sum_univ' x, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  simp only [Matrix.mul_apply, hβ, hM, toLoc, Matrix.map_apply, ← map_mul, ← map_sum, finCongr_refl, Equiv.refl_apply]
  rw [key]
  simp [Formalism.L2.Col.inFr, Matrix.mulVec, dotProduct]

end Mat

theorem twSt_h {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel) {S₀ : Set ℕ}
    (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (m2 j : ℕ)
    (al : (Formalism.L2.Col.twSt Ch sel mu cst m2 j).β) (P : Formalism.L2.Col.rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    (Formalism.L2.Col.twSt Ch sel mu cst m2 j).h al P = 1 := by
  revert al
  cases j with
  | zero => exact fun _ => rfl
  | succ i =>
    rw [Formalism.L2.Col.twSt]
    by_cases h1 : i + 1 ≤ m2
    · rw [if_pos h1]
      exact fun _ => dif_neg fun h => (@Finset.mem_sdiff _ (_) _ _ _).1 h |>.2 hP
    · rw [if_neg h1]
      by_cases h2 : i + 1 = m2 + 1
      · rw [if_pos h2]
        exact fun _ => rfl
      · rw [if_neg h2]
        exact fun al => al.elim

section World
open Formalism.L2.Col

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {v : B.Word} {Ch : ℕ → Type}
  {A : ColDat I l Z v Ch} {a : XPart (I.rec7 l Z) v} {ζ₀ : Fin a.Lz.rank → (I.rec7 l Z).host.E}
  {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} {G : GX a ζ₀ PP} {P : rowSG (B.primes X) I.sel (I.tup I.mu0)}

variable (A) in

def ratMap (i : ℕ) (hi : i + 1 ≤ B.R.m) (P : rowSG (B.primes X) I.sel (I.tup I.mu0))
    (γ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) :
    HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) :=
  inFr (frsF I.sel (I.tup I.mu0) (A.p0 i).1.1 P) (frsF I.sel (I.tup I.mu0) (A.p0 (i + 1)).1.1 P)
    (Matrix.toLin' (γ.reindex (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)))))

variable (a) in

def StdLat : Prop := ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.x j).L ∧ ((a.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _

end World

section Main
open Formalism.L2.Col

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {w : World I l Z} {v : B.Word}
  {a : XPart (I.rec7 l Z) v} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {o : OffX a k ((B.primes X).vT v)} {G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1} {A : ColDat I l Z v (w.C.herm.base.Ch v)}

end Main

end GlobalTheory.SeeSaw.StdMatch
end
end
