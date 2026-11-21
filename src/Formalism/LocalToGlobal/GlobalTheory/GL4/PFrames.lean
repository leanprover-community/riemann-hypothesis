import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrGen
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieIdx
import Formalism.LocalToGlobal.GlobalTheory.GL4.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieSep
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

section
noncomputable section

open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

theorem isIntegral_of_trace_pow_mul (E : Type) [Field E] [NumberField E] (x : E)
    (h : ∀ (n : ℕ) (b : 𝓞 E), Algebra.trace ℚ E (x ^ n * (b : E)) ∈ (algebraMap ℤ ℚ).range) :
    IsIntegral ℤ x := by
  classical
  let B := Algebra.traceForm ℚ E
  let b0 := NumberField.integralBasis E
  let Dl : Submodule ℤ E := B.dualSubmodule (Submodule.span ℤ (Set.range b0))
  have hDl : Dl = Submodule.span ℤ (Set.range (B.dualBasis (traceForm_nondegenerate ℚ E) b0)) :=
    LinearMap.BilinForm.dualSubmodule_span_of_basis B _ b0
  have hDfg : Dl.FG := by
    rw [hDl]; exact Submodule.fg_span (Set.finite_range _)
  let N : Submodule ℤ E := Submodule.span ℤ (Set.range (fun p : ℕ × 𝓞 E => x ^ p.1 * (p.2 : E)))
  have hND : N ≤ Dl := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨n, b⟩, rfl⟩
    intro y hy
    rw [NumberField.mem_span_integralBasis] at hy
    obtain ⟨c, rfl⟩ := hy
    obtain ⟨z, hz⟩ := h n (b * c)
    refine Submodule.mem_one.2 ⟨z, ?_⟩
    rw [hz]
    show _ = Algebra.trace ℚ E (x ^ n * (b : E) * (c : E))
    push_cast [mul_assoc]
    rfl
  have hNfg : N.FG := by
    have hn : IsNoetherian ℤ Dl := isNoetherian_of_fg_of_noetherian Dl hDfg
    exact isNoetherian_submodule.1 hn N hND
  have hN0 : N ≠ ⊥ := by
    intro h0
    have : x ^ 0 * ((1 : 𝓞 E) : E) ∈ N := Submodule.subset_span ⟨(0, 1), rfl⟩
    rw [h0] at this
    simp at this
  refine isIntegral_of_smul_mem_submodule (A := E) N hN0 hNfg x fun n hn => ?_
  refine Submodule.span_induction (p := fun n _ => x • n ∈ N) ?_ ?_ ?_ ?_ hn
  · rintro _ ⟨⟨k, b⟩, rfl⟩
    refine Submodule.subset_span ⟨(k + 1, b), ?_⟩
    show x ^ (k + 1) * (b : E) = x * (x ^ k * (b : E))
    ring
  · simp
  · intro a b _ _ ha hb; rw [smul_add]; exact add_mem ha hb
  · intro r a _ ha; rw [smul_comm]; exact N.smul_mem r ha

theorem mem_int_of_adele (F : Type) [Field F] [NumberField F] (y : F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) y ∈ intAd F) : y ∈ (algebraMap (𝓞 F) F).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro v
  have := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  exact this

section Tens

variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

theorem mul_mem_pureClosure {R : Type} [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R)
    {m m' : E ⊗[F] R}
    (hm : m ∈ AddSubgroup.closure {z | ∃ a ∈ S₁, ∃ r ∈ S₂, z = a ⊗ₜ[F] r})
    (hm' : m' ∈ AddSubgroup.closure {z | ∃ a ∈ S₁, ∃ r ∈ S₂, z = a ⊗ₜ[F] r}) :
    m * m' ∈ AddSubgroup.closure {z | ∃ a ∈ S₁, ∃ r ∈ S₂, z = a ⊗ₜ[F] r} := by
  induction hm using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, r, hr, rfl⟩ := hx
    induction hm' using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a', ha', r', hr', rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a * a', S₁.mul_mem ha ha', r * r', S₂.mul_mem hr hr',
        Algebra.TensorProduct.tmul_mul_tmul _ _ _ _⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add y y' _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h1 => rw [neg_mul]; exact neg_mem h1

theorem tensInt_le_pureClosure {R : Type} [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R)
    {z : E ⊗[F] R} (hz : z ∈ tensInt (F := F) R S₁ S₂) :
    z ∈ AddSubgroup.closure {z | ∃ a ∈ S₁, ∃ r ∈ S₂, z = a ⊗ₜ[F] r} := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨r, rfl⟩
    · exact AddSubgroup.subset_closure ⟨a, a.2, 1, S₂.one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, S₁.one_mem, r, r.2, rfl⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, S₁.one_mem, 1, S₂.one_mem, rfl⟩
  | add x y _ _ h1 h2 => exact add_mem h1 h2
  | neg x _ h1 => exact neg_mem h1
  | mul x y _ _ h1 h2 => exact mul_mem_pureClosure S₁ S₂ h1 h2

end Tens

def trT (F E R : Type) [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] : E ⊗[F] R →ₗ[F] R :=
  TensorProduct.lift ((LinearMap.mul F R).comp ((Algebra.linearMap F R).comp (Algebra.trace F E)))

theorem trT_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (a : E) (r : R) :
    trT F E R (a ⊗ₜ r) = algebraMap F R (Algebra.trace F E a) * r := by
  simp [trT]

theorem mem_intOE_of_inclE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsScalarTower ℚ F E] (x : E)
    (hx : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) x ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
    x ∈ (algebraMap (𝓞 E) E).range := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

  have htrO : ∀ a : E, a ∈ intOE E → Algebra.trace F E a ∈ (algebraMap (𝓞 F) F).range := by
    rintro a ⟨a, rfl⟩
    have : IsIntegral ℤ (Algebra.trace F E (a : E)) := Algebra.isIntegral_trace a.2
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 this
    exact ⟨y, hy⟩

  have htr : ∀ z ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F),
      trT F E (FiniteAdeleRing (𝓞 F) F) z ∈ intAd F := by
    intro z hz
    have := tensInt_le_pureClosure _ _ hz
    clear hz
    induction this using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, r, hr, rfl⟩ := hy
      rw [trT_tmul]
      refine (intAd F).mul_mem ?_ hr
      obtain ⟨o, ho⟩ := htrO a ha
      rw [← ho]
      intro v
      show ((o : F) : v.adicCompletion F) ∈ _
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact HeightOneSpectrum.valuation_le_one v o
    | zero => rw [map_zero]; exact zero_mem _
    | add y y' _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [map_neg]; exact neg_mem h1
  have hint : IsIntegral ℤ x := by
    apply isIntegral_of_trace_pow_mul E x
    intro n b
    have hw : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x ^ n * (b : E)) ∈
        tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
      rw [map_mul, map_pow]
      refine Subring.mul_mem _ (Subring.pow_mem _ hx n) (Subring.subset_closure (Or.inl ⟨⟨(b : E), b, rfl⟩, rfl⟩))
    have h1 := htr _ hw
    have e1 : trT F E (FiniteAdeleRing (𝓞 F) F) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x ^ n * (b : E))) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (Algebra.trace F E (x ^ n * (b : E))) := by
      show trT F E _ ((x ^ n * (b : E)) ⊗ₜ 1) = _
      rw [trT_tmul, mul_one]
    rw [e1] at h1
    obtain ⟨o, ho⟩ := mem_int_of_adele F _ h1
    rw [← Algebra.trace_trace (R := ℚ) (S := F) (T := E), ← ho]
    have : IsIntegral ℤ (Algebra.trace ℚ F (o : F)) := Algebra.isIntegral_trace o.2
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 this
    exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint
  exact ⟨y, hy⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

open NumberField Formalism.UG IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem pair_of_mem_dualL (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) {b : Fin S.rank → E} (hb : b ∈ Formalism.L2.Herm.dualL hc S Λ) :
    ∀ a ∈ Λ, hform (hc.sig : E →+* E) S.gram a b ∈ (algebraMap (𝓞 E) E).range := by
  intro a ha
  unfold Formalism.L2.Herm.dualL at hb
  induction hb using Submodule.span_induction with
  | mem b hb => exact hb a ha
  | zero => rw [Formalism.UG.P.csScale_hform_zero_right]; exact zero_mem _
  | add b b' _ _ h h' => rw [Formalism.UG.P.csScale_hform_add_right]; exact add_mem h h'
  | smul r b _ h =>
    rw [← algebraMap_smul E r b, Formalism.UG.P.csScale_hform_smul_right]
    exact mul_mem ⟨r, rfl⟩ h

theorem ClassTie.lat_int {hc : Formalism.BasicNotions.CMData F E} {S : Formalism.BasicNotions.HSpace E} {Lb : Submodule (𝓞 E) (Fin S.rank → E)}
    {U : Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F))} {cls : Type} {stab : cls → Type}
    [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}
    (X : Formalism.L2.Herm.ClassTie hc S Lb U stab lat) (hLb : Lb ≤ Formalism.L2.Herm.dualL hc S Lb) (c : cls)
    {x y : S.V} (hx : x ∈ lat c) (hy : y ∈ lat c) : S.hT x y ∈ (algebraMap (𝓞 E) E).range := by
  have : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  apply mem_intOE_of_inclE F E
  have hm : ∀ a ∈ Lb, ∀ b ∈ Lb, IsIntegral ℤ (((1 : ℤ) : E) * hform (hc.sig : E →+* E) S.gram a b) := by
    intro a ha b hb
    obtain ⟨o, ho⟩ := pair_of_mem_dualL hc S Lb (hLb hb) a ha
    rw [Int.cast_one, one_mul, ← ho]
    exact RingOfIntegers.isIntegral_coe o
  have hglob : ∀ z ∈ lat c, Formalism.L2.Herm.crd S z ∈ Formalism.UG.CS.globLat (X.y c : GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)) Lb := by
    intro z hz
    show _ ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) _ Lb
    refine ((X.y_lat c _).1 ?_)
    exact Submodule.subset_span ⟨Formalism.L2.Herm.crd S z, ⟨z, hz, rfl⟩, rfl⟩
  have key := Formalism.UG.P.csScale_glob hc.sig S.gram Lb 1 hm (X.y c) (X.y c).2 (hglob x hx) (hglob y hy)
  rw [Int.cast_one, one_mul] at key
  rw [Formalism.L2.Herm.hT_crd hc]
  exact key

theorem ColLevel.lat_int {R : Formalism.BasicNotions.Ranks} {sp : Formalism.BasicNotions.Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hcp : ι → Formalism.BasicNotions.HCParam R} {C : Formalism.BasicNotions.ColumnChain R ι hcp}
    {A : Formalism.BasicNotions.ColumnsAtT R C} {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    (L : Formalism.BasicNotions.ColLevel R F E sp gp C A clsLat) (c : C.cls 0)
    {x y : (sp.X 0).V} (hx : x ∈ clsLat 0 c) (hy : y ∈ clsLat 0 c) :
    (sp.X 0).hT x y ∈ (algebraMap (𝓞 E) E).range := by
  have : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  apply mem_intOE_of_inclE F E
  have hm : ∀ a ∈ L.Lb, ∀ b ∈ L.Lb,
      IsIntegral ℤ (((1 : ℤ) : E) * hform (sp.cm.sig : E →+* E) sp.gram0 a b) := by
    intro a ha b hb
    obtain ⟨o, ho⟩ := L.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← ho]
    exact RingOfIntegers.isIntegral_coe o
  have hglob : ∀ z ∈ clsLat 0 c,
      sp.crd0 z ∈ Formalism.UG.CS.globLat (L.y c : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) L.Lb := by
    intro z hz
    show _ ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) _ L.Lb
    refine ((L.y_lat c _).1 ?_)
    exact Submodule.subset_span ⟨sp.crd0 z, ⟨z, hz, rfl⟩, rfl⟩
  have key := Formalism.UG.P.csScale_glob sp.cm.sig sp.gram0 L.Lb 1 hm (L.y c) (L.y c).2 (hglob x hx) (hglob y hy)
  rw [Int.cast_one, one_mul] at key
  rw [sp.hermitianForm_base_coordinates]
  exact key

end General

open Formalism.BasicNotions in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem clsLat_int {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m)
    (c : (D.mem u).C.cls i) :
    ∀ x ∈ D.clsLat u i c, x ∈ Formalism.MainNotions.flipTwoThree.dualSub (D.sp.X i) (D.clsLat u i c) := by
  intro x hx y hy
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact ColLevel.lat_int (X.base.lev0 u) c hy hx
  · exact ClassTie.lat_int (X.base.cls u i h1 hi) (X.base.lev u i h1 hi).Lb_int c hy hx

open Formalism.BasicNotions in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem clsLatP_int {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) (c : (D.fm u).clsP) :
    ∀ x ∈ (X.atT u).lattice₂ c, x ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' ((X.atT u).lattice₂ c) := by
  intro x hx y hy
  refine ClassTie.lat_int (X.atT u).clsP ?_ c hy hx
  rw [Formalism.L2.Herm.coordinate_lattice_self_dual]

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar


def FramesStep (D : D7) (u : D.what₂.Word) (i : ℕ) : Prop :=
  ∃ e : (D.mem u).C.cls i → Fin (D.R.N i) → (D.sp.X i).V,
    (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub (D.sp.X i) (D.clsLat u i c)) ∧
    ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls (D.sp.X i) (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) (D.clsLat u i c)
      (D.clsLat u i c') (e c) (e c') → c = c'

def ClauseP (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ LP : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V,
    (∀ c, Submodule.IsLattice D.host.E (LP c) ∧ Formalism.MainNotions.flipTwoThree.LatT D.sp.X' 1 (LP c)) ∧
    ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
      (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' (LP c)) ∧
      ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls D.sp.X' (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) (LP c) (LP c') (e c) (e c') →
        c = c'


end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_int (a : 𝓞 E) : star (a : E) ∈ (algebraMap (𝓞 E) E).range := by
  exact ⟨RingOfIntegers.mapRingHom (starRingEnd E) a, rfl⟩

theorem dual_le_of_split (S S' : HSpace E) (ι : S'.V →ₗ[E] S.V) (hι : HSpace.IsIsomEmb S' S ι) (z0 : S.V)
    (horth : ∀ x, S.hT (ι x) z0 = 0) (T : ℕ) (hT0 : T ≠ 0) (hz0 : S.hT z0 z0 = (T : E))
    (γ : S.V ≃ₗ[E] S.V) (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (hint : L ≤ Formalism.HermitianLatticesTheory.dual S.hT L)
    (hidx : L.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup = T ^ Module.finrank ℚ E)
    (L' : Submodule (𝓞 E) S'.V)
    (htil : Formalism.HermitianLatticesTheory.gmap γ L = L'.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) :
    Formalism.HermitianLatticesTheory.dual S'.hT L' ≤ L' := by
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT0
  have horth' : ∀ x, S.hT z0 (ι x) = 0 := by
    intro x
    have := S.herm.eq (ι x) z0
    rw [horth, map_zero] at this
    exact this.symm

  have huniq : ∀ (v : S'.V) (t : E), ι v + t • z0 = 0 → v = 0 ∧ t = 0 := by
    intro v t h
    have h1 : S.hT z0 (ι v + t • z0) = 0 := by rw [h, map_zero]
    rw [map_add, map_smul, horth', hz0, smul_eq_mul, zero_add, mul_eq_zero] at h1
    have ht : t = 0 := h1.resolve_right hTE
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at h
    apply S'.nondeg.2 v
    intro x
    rw [← hι, h, map_zero]

  have hdec : ∀ l ∈ L, ∃ l' ∈ L', ∃ a : 𝓞 E, γ l = ι l' + (a : E) • z0 := by
    intro l hl
    have : γ l ∈ Formalism.HermitianLatticesTheory.gmap γ L := ⟨l, hl, rfl⟩
    rw [htil, Submodule.mem_sup] at this
    obtain ⟨y, ⟨l', hl', rfl⟩, w, hw, hsum⟩ := this
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨l', hl', a, by rw [← hsum, algebraMap_smul]; rfl⟩
  have hcomp : ∀ (l' : S'.V), l' ∈ L' → ∀ a : 𝓞 E, γ.symm (ι l' + (a : E) • z0) ∈ L := by
    intro l' hl' a
    have : ι l' + (a : E) • z0 ∈ Formalism.HermitianLatticesTheory.gmap γ L := by
      rw [htil]
      refine Submodule.add_mem_sup ⟨l', hl', rfl⟩ ?_
      exact Submodule.mem_span_singleton.2 ⟨a, (algebraMap_smul E a z0).symm⟩
    obtain ⟨l, hl, he⟩ := this
    have : l = γ.symm (ι l' + (a : E) • z0) := by rw [← he]; simp
    rw [← this]; exact hl
  have hpair : ∀ (v : S'.V) (a t : E), S.hT (ι v + a • z0) (t • z0) = star a * t * (T : E) := by
    intro v a t
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, horth, hz0, smul_eq_mul,
      starRingEnd_apply, zero_add]
    ring
  have hpair2 : ∀ (v x : S'.V) (a : E), S.hT (ι v + a • z0) (ι x) = S'.hT v x := by
    intro v x a
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, horth', smul_zero, add_zero]
    exact hι v x
  set q : S.V := γ.symm ((T : E)⁻¹ • z0) with hq
  have hγq : γ q = (T : E)⁻¹ • z0 := by simp [hq]

  have hqd : q ∈ Formalism.HermitianLatticesTheory.dual S.hT L := by
    rw [Formalism.L2.Herm.mem_dual]
    intro l hl
    obtain ⟨l', _, a, ha⟩ := hdec l hl
    rw [← hγ, ha, hγq, hpair, mul_assoc, inv_mul_cancel₀ hTE, mul_one]
    exact star_int a
  set Q : Submodule (𝓞 E) S.V := L ⊔ Submodule.span (𝓞 E) {q} with hQ
  have hLQ : L ≤ Q := le_sup_left
  have hQd : Q ≤ Formalism.HermitianLatticesTheory.dual S.hT L :=
    sup_le hint ((Submodule.span_singleton_le_iff_mem _ _).2 hqd)

  let φ : 𝓞 E →+ S.V := (LinearMap.toSpanSingleton (𝓞 E) S.V q).toAddMonoidHom
  have hrange : (Submodule.span (𝓞 E) {q}).toAddSubgroup = φ.range := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, AddMonoidHom.mem_range, φ,
      LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply]
  have hcomap : L.toAddSubgroup.comap φ = (Ideal.span {((T : ℕ) : 𝓞 E)}).toAddSubgroup := by
    ext a
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, φ, LinearMap.toAddMonoidHom_coe,
      LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton]
    constructor
    · intro h
      obtain ⟨l', _, b, hb⟩ := hdec _ h
      rw [← algebraMap_smul E a q, map_smul, hγq, smul_smul] at hb
      have h2 := huniq (-l') ((a : E) * (T : E)⁻¹ - (b : E)) (by
        rw [map_neg, sub_smul, hb]; abel)
      have h3 : (a : E) = (T : E) * (b : E) := by
        have := h2.2
        field_simp at this
        linear_combination this
      refine ⟨b, ?_⟩
      apply RingOfIntegers.coe_injective
      push_cast
      exact h3
    · rintro ⟨b, rfl⟩
      convert hcomp 0 (zero_mem _) b using 1
      have e1 : algebraMap (𝓞 E) E (((T : ℕ) : 𝓞 E) * b) = (T : E) * (b : E) := by simp
      rw [map_zero, zero_add, hq, ← algebraMap_smul E (((T : ℕ) : 𝓞 E) * b), e1, ← LinearEquiv.map_smul, smul_smul]
      congr 2
      field_simp
  have hLQi : L.toAddSubgroup.relIndex Q.toAddSubgroup = T ^ Module.finrank ℚ E := by
    rw [hQ, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, hrange, ← AddSubgroup.index_comap,
      hcomap, ← card_quot_nat E T]
    rfl
  have hQi : Q.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup = 1 := by
    have h := AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hLQ)
      (Submodule.toAddSubgroup_mono hQd)
    rw [hLQi, hidx] at h
    have hp : 0 < T ^ Module.finrank ℚ E := pow_pos (Nat.pos_of_ne_zero hT0) _
    exact (Nat.mul_eq_left hp.ne').1 h
  have hdQ : Formalism.HermitianLatticesTheory.dual S.hT L ≤ Q :=
    (Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 hQi)

  intro x hx
  have hw : γ.symm (ι x) ∈ Formalism.HermitianLatticesTheory.dual S.hT L := by
    rw [Formalism.L2.Herm.mem_dual]
    intro l hl
    obtain ⟨l', hl', a, ha⟩ := hdec l hl
    rw [← hγ, ha, LinearEquiv.apply_symm_apply, hpair2]
    exact (Formalism.L2.Herm.mem_dual S' L' x).1 hx l' hl'
  obtain ⟨l, hl, r, hr, hsum⟩ := Submodule.mem_sup.1 (hdQ hw)
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hr
  obtain ⟨l', hl', a, ha⟩ := hdec l hl
  have he : ι x = ι l' + (a : E) • z0 + (b : E) • ((T : E)⁻¹ • z0) := by
    have := congrArg γ hsum
    rw [LinearEquiv.apply_symm_apply, map_add, ha, ← algebraMap_smul E b q, map_smul, hγq] at this
    exact this.symm
  have h2 := huniq (x - l') (-((a : E) + (b : E) * (T : E)⁻¹)) (by
    rw [map_sub, he, neg_smul, add_smul, smul_smul]; abel)
  have : x = l' := sub_eq_zero.1 h2.1
  rw [this]; exact hl'

theorem span_top_of_split (S S' : HSpace E) (ι : S'.V →ₗ[E] S.V) (hι : HSpace.IsIsomEmb S' S ι) (z0 : S.V)
    (horth : ∀ x, S.hT (ι x) z0 = 0) (T : ℕ) (hT0 : T ≠ 0) (hz0 : S.hT z0 z0 = (T : E))
    (γ : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) (hspan : Submodule.span E (L : Set S.V) = ⊤)
    (L' : Submodule (𝓞 E) S'.V)
    (htil : Formalism.HermitianLatticesTheory.gmap γ L = L'.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) :
    Submodule.span E (L' : Set S'.V) = ⊤ := by
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT0
  have horth' : ∀ x, S.hT z0 (ι x) = 0 := by
    intro x
    have := S.herm.eq (ι x) z0
    rw [horth, map_zero] at this
    exact this.symm
  have huniq : ∀ (v : S'.V) (t : E), ι v + t • z0 = 0 → v = 0 ∧ t = 0 := by
    intro v t h
    have h1 : S.hT z0 (ι v + t • z0) = 0 := by rw [h, map_zero]
    rw [map_add, map_smul, horth', hz0, smul_eq_mul, zero_add, mul_eq_zero] at h1
    have ht : t = 0 := h1.resolve_right hTE
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at h
    apply S'.nondeg.2 v
    intro x
    rw [← hι, h, map_zero]
  have key : ∀ w ∈ Submodule.span E ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V),
      ∃ y ∈ Submodule.span E (L' : Set S'.V), ∃ t : E, w = ι y + t • z0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rw [htil, SetLike.mem_coe, Submodule.mem_sup] at hw
      obtain ⟨y, ⟨l', hl', rfl⟩, w', hw', rfl⟩ := hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw'
      exact ⟨l', Submodule.subset_span hl', (a : E), by rw [← algebraMap_smul E a z0]; rfl⟩
    | zero => exact ⟨0, zero_mem _, 0, by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨y, hy, t, rfl⟩ := h
      obtain ⟨y', hy', t', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', t + t', by rw [map_add, add_smul]; abel⟩
    | smul e w _ h =>
      obtain ⟨y, hy, t, rfl⟩ := h
      exact ⟨e • y, Submodule.smul_mem _ e hy, e * t, by rw [smul_add, map_smul, smul_smul]⟩
  have htop : Submodule.span E ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = ⊤ := by
    have : ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = γ '' (L : Set S.V) := by
      ext x; simp [Formalism.HermitianLatticesTheory.gmap]
    rw [this]
    show Submodule.span E ((γ : S.V →ₗ[E] S.V) '' (L : Set S.V)) = ⊤
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact γ.surjective
  rw [eq_top_iff]
  intro v _
  obtain ⟨y, hy, t, he⟩ := key (ι v) (by rw [htop]; exact Submodule.mem_top)
  have h2 := huniq (v - y) (-t) (by rw [map_sub, he, neg_smul]; abel)
  rw [show v = y from sub_eq_zero.1 h2.1]; exact hy

end General

open Formalism.L2.Herm in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem localLattice_selfDual {D : D7} (X : FullTied D) (u : D.what₂.Word) (c : (D.fm u).clsP) :
    Submodule.IsLattice D.host.E ((X.atT u).lattice₂ c) ∧ Formalism.MainNotions.flipTwoThree.LatT D.sp.X' 1 ((X.atT u).lattice₂ c) := by
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have horth : ∀ x, (D.sp.X D.R.m).hT (D.sp.iX' x) (X.atT u).z0 = 0 := by
    intro x
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (X.atT u).cocycle_zero_mem_invariants
    rw [← ht, map_smul, D.sp.z_orth, smul_zero]
  set L := D.clsLat u D.R.m ((D.fm u).til c)
  have hint : L ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X D.R.m).hT L := by
    intro x hx
    have := clsLat_int X u D.R.m le_rfl _ x hx
    rw [dualSub_eq] at this
    exact this
  have hidx : L.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual (D.sp.X D.R.m).hT L).toAddSubgroup =
      (D.mem u).A.T ^ Module.finrank ℚ D.host.E := by
    have := clsLat_index X u D.R.m le_rfl ((D.fm u).til c)
    rw [dualSub_eq] at this
    rw [this, finrank_E]; rfl
  have htil := ((X.atT u).til_tie c).1
  have hle := dual_le_of_split (D.sp.X D.R.m) D.sp.X' D.sp.iX' D.sp.iX'_isom (X.atT u).z0 horth
    (D.mem u).A.T hT0 (X.atT u).hermitianForm_lastCoordinateUniformizerVector_self ((X.atT u).tilG c).1 ((X.atT u).tilG c).2 L hint hidx _ htil
  have hsp := span_top_of_split (D.sp.X D.R.m) D.sp.X' D.sp.iX' D.sp.iX'_isom (X.atT u).z0 horth
    (D.mem u).A.T hT0 (X.atT u).hermitianForm_lastCoordinateUniformizerVector_self ((X.atT u).tilG c).1 L (D.clsLat_lat u D.R.m _).span_eq_top _ htil
  refine ⟨⟨?_, hsp⟩, clsLatP_int X u c, ?_⟩
  ·
    have hfgM : (Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L).FG := (D.clsLat_lat u D.R.m _).fg.map _
    have hle' : ((X.atT u).lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ≤
        Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L := by rw [htil]; exact le_sup_left
    have hn : IsNoetherian (𝓞 D.host.E) (Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L) :=
      isNoetherian_of_fg_of_noetherian _ hfgM
    have hfg := isNoetherian_submodule.1 hn _ hle'
    refine Submodule.fg_of_fg_map_injective _ ?_ hfg
    intro a b hab
    have h0 : D.sp.iX' (a - b) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hab
    refine sub_eq_zero.1 (D.sp.X'.nondeg.2 _ fun x => ?_)
    rw [← D.sp.iX'_isom, h0, map_zero]
  · rw [dualSub_eq]
    exact AddSubgroup.relIndex_eq_one.2 ((Submodule.toAddSubgroup_le _ _).2 hle)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FramesP {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) : Prop :=
  ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
    (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' ((X.atT u).lattice₂ c)) ∧
    ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls D.sp.X' (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) ((X.atT u).lattice₂ c)
      ((X.atT u).lattice₂ c') (e c) (e c') → c = c'




end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem isLattice_between {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (A B : Submodule (𝓞 E) W) (hA : Submodule.IsLattice E A) (hAB : A ≤ B) (T : ℕ) (hT : T ≠ 0)
    (hTB : ∀ x ∈ B, (T : E) • x ∈ A) : Submodule.IsLattice E B := by
  let f : W →ₗ[𝓞 E] W := ((T : ℕ) : 𝓞 E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((T : ℕ) : E) • x = ((T : ℕ) : E) • y := by
      simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective W (by exact_mod_cast hT : ((T : ℕ) : E) ≠ 0) h1
  have hmap : B.map f ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hTB x hx
    simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using h1
  haveI : IsNoetherian (𝓞 E) A := isNoetherian_of_fg_of_noetherian A hA.fg
  have hmfg : (B.map f).FG := by
    have h1 := IsNoetherian.noetherian ((B.map f).comap A.subtype)
    have h2 := h1.map A.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hmap] at h2
  exact ⟨Submodule.fg_of_fg_map_injective f hf hmfg,
    eq_top_iff.2 (le_trans (le_of_eq hA.span_eq_top.symm) (Submodule.span_mono (SetLike.coe_subset_coe.2 hAB)))⟩


end Gen

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar







end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
