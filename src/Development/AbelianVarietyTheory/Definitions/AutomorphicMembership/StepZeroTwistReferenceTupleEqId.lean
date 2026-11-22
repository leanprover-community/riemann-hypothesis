module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology
open scoped TensorProduct

namespace GlobalTheory.Mem.ColAd

section Form

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : InfF D) (V : HSp D) {n : ℕ} [NeZero n] (hn : V.rank = n) {ι : Type} [Fintype ι] (t : ι ≃ D.what₂.Tau)
  {K : Type} [Field K] [NumberField K] [StarRing K] (emb : ι → D.host.E →+* K) (σ : K →+* ℂ)
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (S : GStep D.host.E K n) (b : S.β)
  (pt : DecoF D.host.E n ST SG Q → S.D b) (c : ℕ) (x₀ : GL (Fin n) (AfE D.host.F D.host.E)) (l : (Fr emb σ n → ℂ) →ₗ[ℂ] ℂ)

variable {S b pt c emb σ} {lam : ι → DomWeight n} {φ : S.Cl → Fr emb σ n → ℂ}

variable {V x₀}

end Form

end GlobalTheory.Mem.ColAd

namespace GlobalTheory.Mem.Col2.ColIn

open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr

attribute [local instance] starE

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

instance neZeroN (R : Ranks) (j : ℕ) : NeZero (R.N j) := ⟨(R.N_pos j).ne'⟩

instance neZeroN' (R : Ranks) : NeZero (R.N R.m - 1) := ⟨by have := R.m_add_three_le_k; unfold Ranks.N; omega⟩

theorem zero_succ_ne (R : Ranks) : 0 + 1 ≠ R.m := by have := R.two_le_m; omega

variable {I}

theorem Ok.gram_X (h : I.Ok) (j : ℕ) : (B.sp.X j).gram = 1 := by
  obtain ⟨hs, h1, -⟩ := h.spaces
  rw [h1 j]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem Ok.exists_isPtOf (h : I.Ok) (u : B.Word) (a : I.ι) {n : ℕ}
    (p : DecoF B.host.E n ((B.primes X).vT u) (B.primes X).vGs (I.Q a)) : ∃ x, IsPtOf B.sp.cm x p := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hd : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup a)) := Finset.disjoint_left.2 fun P h1 h2 =>
    GlobalTheory.Proof.NarrowJetMoments.notMem_rowSG hPr h.sel_ok (hPr.T_prime u) (h.T_mem u) (hPr.T_ne_g u) h2 (T_mem_vT hPr u ⟨P, h1⟩)
  refine PtExist.exists_isPtOf_cm B.sp.cm n _ _ _ p (hd.mono_right Finset.subset_union_left) (hd.mono_right Finset.subset_union_right)
    ((LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)) fun P hP => ?_
  have h1 := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem P
  unfold Sall at h1
  simp only [Finset.mem_union] at h1 hP ⊢
  exact (h1 hP).1

end GlobalTheory.Mem.Col2.ColIn

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Col2.ColIn (zero_succ_ne)

attribute [local instance] starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

variable {I}

variable (h : I.Ok) (l : I.Laws) (Z : Later B (I.cols l)) {θ : InfF (I.rec7 l Z)} (hθ : IsInfFam θ)

include l in
theorem idx_zero_eq (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) (c : (I.stp u a 0).Cl) : c.1 = b := by
  obtain ⟨c', rfl⟩ := (l.bij0 u a b).2 c
  rfl

theorem stepZeroTwist_reference_tuple_eq_id (u : B.Word) (φ : (I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) :
    (I.cols l).e0Tw u I.mu0 φ = φ := by
  have key : ∀ c, I.eCls0 l u I.mu0 c = c := fun c => by
    obtain ⟨b, q⟩ := c
    obtain rfl : b = (l.idx0 I.mu0).some := idx_zero_eq l u _ _ ⟨b, q⟩
    have e : I.pt0 u I.mu0 I.mu0 ((I.stp u I.mu0 0).rep ⟨_, q⟩) = (I.stp u I.mu0 0).rep ⟨_, q⟩ := by
      have := ((I.stp u I.mu0 0).rep ⟨_, q⟩).2
      rw [ysAt_ys_of_ne I.sel _ _ (zero_succ_ne B.R)] at this
      exact Subtype.ext (Prod.ext (extTo_self (I.twistPrimes_reference_tuple_eq_empty.symm ▸ Finset.disjoint_empty_right _ : Disjoint _ (I.Q I.mu0)) _) (Eq.symm this))
    show (I.stp u I.mu0 0).cl _ (I.pt0 u I.mu0 I.mu0 _) = _
    rw [e]
    exact congrArg (Sigma.mk _) ((I.stp u I.mu0 0).rp_spec _ q)
  funext c
  exact congrArg φ ((Equiv.symm_apply_eq _).2 (key c).symm)

end GlobalTheory.Mem.Col2.TC

end
