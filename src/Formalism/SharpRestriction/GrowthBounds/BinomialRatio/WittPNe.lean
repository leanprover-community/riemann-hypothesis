import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def topOdd (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT :=
  ⟨segPos X.TT j i, (pos_mem X.TT j i).1⟩

def topEnd (X : Loc) (j : Fin (numSeg X.TT)) : X.TT :=
  ⟨segNext X.TT j, (next_mem X.TT j).1⟩

def symVar (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → (X.TT × Bool) × Fin (X.m + 1)
  | Sum.inl (a, c) =>
    if h : (a : ℕ) < 2 * segS X.TT j then
      ((topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0)), c.succ)
    else ((topEnd X j, decide ((a : ℕ) = 2 * segS X.TT j)), c.succ)
  | Sum.inr (l, b) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then
      ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩), !b), 0)
    else ((topEnd X j, !b), 0)

def symLev (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ
  | Sum.inl (a, _) =>
    if h : (a : ℕ) < 2 * segS X.TT j then (X.seg C0 CE1 CE2 j).P p ⟨(a : ℕ) / 2, by omega⟩ else 1
  | Sum.inr (l, _) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then (X.seg C0 CE1 CE2 j).P p (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩) else 1

def digitMon (K : Type*) [CommSemiring K] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
    MvPolynomial.X ((topOdd X j i, true), c) ^ b.rz i c * MvPolynomial.X ((topOdd X j i, false), c) ^ b.ry i c

def sTopMon (K : Type*) [CommSemiring K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
    MvPolynomial.X ((topOdd X j i, true), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * (coarseA p (X.seg C0 CE1 CE2 j) b i - b.w i)) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * b.sg i)
  else 1

def ioBlock (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  digitMon K C0 CE1 CE2 X j b * sTopMon K p C0 CE1 CE2 X j b *
    aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^
      symLev p C0 CE1 CE2 X j v) u

def symFam (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ j, ioBlock K p C0 CE1 CE2 X j (β j) (s j)

def Lemma44At (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) (β j)).SSZ O (r := X.m)) →
      ∃ F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
        InA (C (algebraMap O (KK O) (S.w ^ (∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)))) * F) ∧
        InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c ∧
        ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
          ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 g → InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g' F X.c

def BinomialRatioBeyondThreshold : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => Lemma44At C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def IsFlatTheta {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O) (φ : WF p n' ≃+* W) {m : ℕ} (TT : Finset (Fin n'))
    (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT)) : Prop :=
  letI : Algebra (WF p n') O := algOfIdent jO φ
  (∀ F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O),
      InA (O := O) (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) ↔
      Θ F ∈ HHL (O := O) ι σ TT aT bT (colSpan W h)) ∧
    (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
      ∀ e : Edge W Qq (m + 1), IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
        ∀ (F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (i : ℕ),
          InWjRg p n' O w 1 (hhLetters TT) g (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) i ↔
          Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (ReHH p ι σ w TT aT bT e)) ∧
    ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e → e.src = colSpan W h →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g ∧ IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose)

def SrcHalfAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → 1 ≤ X.c →
    ∀ φ : WF X.p X.n' ≃+* W, IsWittIdent σ φ →
    ∀ (h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) Qq) Θ, IsFlatTheta ι σ jO w φ X.TT X.aT X.bT h Θ →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e → e.src = colSpan W h →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
      IsEdgeBasis X.p 1 e (h * ((matQ φ g)⁻¹).transpose) →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (X.m0 Cm) (β j)).SSZ O (r := X.m)) →
      ∃ F, Θ F ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e ∧
        (letI : Algebra (WF X.p X.n') O := algOfIdent jO φ
         InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) g
           (F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def MonoAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p r : ℕ) [NeZero r] {s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ)
    (b : SegBlock s r) (m m' : ℝ), m ≤ m' →
    (blockData p S aTop aPlus m' b).SSZ O (r := r) ≤ (blockData p S aTop aPlus m b).SSZ O (r := r)

def PlaneAt : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] (m : ℕ) (φ : WF p n' ≃+* W) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (e e' : Edge W Qq (m + 1)), IsFractionRing W Qq →
    IsGLW g → IsGLW g' → IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
    IsEdgeBasis p 1 e' (h * ((matQ φ g')⁻¹).transpose) → ratPlane p n' 1 g' = ratPlane p n' 1 g → e' = e

def SymIntAt (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (mm : ℝ)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)),
    (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)).SSZ O
      (r := X.m)) →
    InA (O := O) (symFam (KK O) X.p C0 CE1 CE2 X β s)

theorem scale_one_mem {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {M : Submodule O V} {x : V} (hx : x ∈ scale (1 : Kf) M) : x ∈ M := by
  simp only [scale, Submodule.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy


end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem ycond_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) {M M' : WithTop ℤ}
    (h : M' ≤ M) : YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j M := by
  unfold YCond
  apply sSup_le_sSup
  rintro S ⟨hS1, hS2⟩
  refine ⟨le_trans hS1 ?_, hS2⟩
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm => le_trans (hx hm) h

theorem yjt_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ)
    {M M' : Fin q → WithTop ℤ} (h : ∀ k, M' k ≤ M k) : Yjt K (r := r) LL J M' ≤ Yjt K (r := r) LL J M :=
  inf_le_inf_left _ (iInf_mono fun k => ycond_mono' (K := K) (r := r) LL (J k) (h k))

theorem map_floor_mono (x : WithTop ℤ) {m m' : ℝ} (h : m ≤ m') :
    x.map (fun y : ℤ => ⌊(y : ℝ) - m'⌋) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - m⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    exact Int.floor_mono (by linarith)

theorem monoAt : MonoAt := by
  intro O _ _ p r _ s S aTop aPlus b m m' hmm
  unfold BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ (fun k => map_floor_mono _ hmm) hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev IntAlg (O : Type) [CommRing O] [IsDomain O] (σ : Type*) : Subalgebra O (MvPolynomial σ (KK O)) :=
  (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)).range

theorem X_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ : Type*} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntAlg O σ := by
  exact (AlgHom.mem_range _).mpr ⟨MvPolynomial.X v, by simp⟩

theorem intPol_le (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntPol O σ) :
    P ∈ IntAlg O σ := by
  obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp h
  exact (AlgHom.mem_range _).mpr ⟨Q, hQ⟩

theorem inA_of_mem (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) :
    InA (O := O) P := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  unfold InA
  intro m
  exact ⟨Q.coeff m, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]⟩

theorem rename_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → τ) {P : MvPolynomial σ (KK O)}
    (h : P ∈ IntAlg O σ) : rename f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  exact (AlgHom.mem_range _).mpr ⟨rename f Q, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_rename]⟩

theorem aeval_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → MvPolynomial τ (KK O))
    (hf : ∀ v, f v ∈ IntAlg O τ) {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) : aeval f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  have e : (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)) Q =
      MvPolynomial.map (algebraMap O (KK O)) Q := rfl
  rw [e, MvPolynomial.aeval_map_algebraMap]
  clear h e
  induction Q using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hf v)

theorem ssz_le_intAlg (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    ∀ x ∈ D.SSZ O (r := r), x ∈ IntAlg O (BVar N r D.T.t) := by
  intro x hx
  unfold BlockData.SSZ at hx
  refine Submodule.span_induction (p := fun x _ => x ∈ IntAlg O (BVar N r D.T.t)) ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, _, y, hy, g0, hg0, rfl⟩ := hx
    have hX := fun v => X_mem_intAlg O (σ := BVar N r D.T.t) v
    have hE : ∀ i, D.Ehat O (r := r) i ∈ IntAlg O (BVar N r D.T.t) := fun i => by
      unfold BlockData.Ehat
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    have hP : D.Eplus O (r := r) ∈ IntAlg O (BVar N r D.T.t) := by
      unfold BlockData.Eplus
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem
      ((IntAlg O _).mul_mem ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hE i) _)
        ((IntAlg O _).pow_mem hP _)) ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hX _) _))
      ((IntAlg O _).pow_mem (hX _) _)) (rename_mem_intAlg O _ (intPol_le O hy.2))) (intPol_le O hg0.2)
  · exact (IntAlg O _).zero_mem
  · intro x y _ _ hx hy; exact (IntAlg O _).add_mem hx hy
  · intro a x _ hx; exact (IntAlg O _).smul_mem hx a

theorem symIntAt (C0 CE1 CE2 : ℝ) : SymIntAt C0 CE1 CE2 := by
  intro X _ O _ _ mm β s hs
  apply inA_of_mem
  unfold symFam
  refine (IntAlg O _).prod_mem fun j _ => ?_
  unfold ioBlock
  have hX := fun v => X_mem_intAlg O (σ := (X.TT × Bool) × Fin (X.m + 1)) v
  refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ?_ ?_) ?_
  · unfold digitMon
    exact (IntAlg O _).prod_mem fun i _ => (IntAlg O _).prod_mem fun c _ =>
      (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
  · unfold sTopMon
    refine (IntAlg O _).prod_mem fun i _ => ?_
    split_ifs
    · exact (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
    · exact (IntAlg O _).one_mem
  · have hsj : s j ∈ IntAlg O (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) :=
      ssz_le_intAlg O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)) (s j) (hs j)
    exact aeval_mem_intAlg O _ (fun v => (IntAlg O _).pow_mem (hX _) _) hsj



end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.Pf14

theorem wittVector_prime_ne_zero (p n' : ℕ) [Fact p.Prime] : ((p : ℕ) : WF p n') ≠ 0 := by
  intro h
  have h1 := WittVector.coeff_p_one (p := p) (R := GaloisField p n')
  rw [h] at h1
  simp at h1

theorem planeAt : PlaneAt := by
  intro p n' _ W Qq _ _ _ _ _ m φ h g g' e e' hfr hg hg' he he' hpl
  have hp0 : (p : W) ≠ 0 := by
    intro h0
    apply wittVector_prime_ne_zero p n'
    apply φ.injective
    rw [map_natCast, h0, map_zero]
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h1 => hp0 ((IsFractionRing.injective W Qq) (by rw [h1, map_zero]))
  obtain ⟨-, hs, ht⟩ := he
  obtain ⟨-, hs', ht'⟩ := he'
  rw [src_eq φ g hg h] at hs
  rw [src_eq φ g' hg' h] at hs'
  rw [matQ_inv φ g hg] at ht
  rw [matQ_inv φ g' hg'] at ht'
  change e.tgt = colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht
  change e'.tgt = colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht'
  obtain ⟨s, t⟩ := e
  obtain ⟨s', t'⟩ := e'
  simp only at hs hs' ht ht'
  rw [Edge.mk.injEq]
  refine ⟨by rw [hs, hs'], ?_⟩
  rw [ht, ht']
  apply le_antisymm
  · exact tgt_le_of_plane φ 1 hpQ g' g hg' hg h hpl.le
  · exact tgt_le_of_plane φ 1 hpQ g g' hg hg' h hpl.ge

end Formalism.MainNotions.ColumnSystems.Pf
end
end
