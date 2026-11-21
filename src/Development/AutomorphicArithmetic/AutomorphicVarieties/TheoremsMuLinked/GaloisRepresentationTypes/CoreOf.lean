import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdVan2
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FiniteCocyclesMatrixRepresentationOfPhiCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FinDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.DetGCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.PolNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.RedBChiComap
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.EpsDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.regDet :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)] [IsScalarTower ℤ_[l] O (Qbar l)] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), 1 ≤ n → PhiCond F.G₀ l → (∃ g : F.G₀, F.ε g ≠ 1) → Continuous ρ → Th.TypeI F ρ → Th.N3 F ρ → Th.RegDet F O ρ P := by
  intro l _ F O _ _ _ _ n ρ P hn hΦ hε hρ hI h3
  classical
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  have halg : ∀ x : ℤ_[l], algebraMap ℤ_[l] (Qbar l) x = algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l]) :=
    fun x => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x
  have hχ : ∀ g : F.G₀, ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) (((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [← halg, IsScalarTower.algebraMap_apply ℤ_[l] O (Qbar l)]
    rfl
  have hχc : Continuous fun g : F.G₀ => ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) := by
    simp only [hχ]
    have h1 : Continuous fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)
    exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp h1)
  have hm : Continuous fun g => W.mat ρ g := Units.continuous_val.comp hρ
  have hm' : Continuous fun g : F.G₀ => W.mat ρ g⁻¹ := hm.comp continuous_inv
  let R : Representation (Qbar l) F.G₀ (Matrix (Fin n) (Fin n) (Qbar l)) :=
    Loc.twist (F.eps O (Qbar l)) (Loc.adGL ρ)
  have hR : ∀ g X, R g X =
      ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) • (W.mat ρ g * X * W.mat ρ g⁻¹) := fun g X => by
    have e : W.mat ρ g⁻¹ = Units.val (ρ g)⁻¹ := by
      rw [← map_inv ρ g]; rfl
    rw [e]
    rfl
  haveI : Module.Finite (Qbar l) (Z1 R) := Det.finite_cocycles_matrixRepresentation_of_phiCond R hΦ fun X => by
    simp only [hR]
    exact hχc.smul ((hm.mul continuous_const).mul hm')
  let S : Type := {σ : F.G₀ // σ ∈ F.G' ∧ (W.mat ρ σ).charpoly.Separable}
  let f : S → ℕ → Z1 R →ₗ[Qbar l] Qbar l := fun σ k =>
    { toFun := fun z => (z.1 σ.1 * W.mat ρ σ.1 ^ k).trace
      map_add' := fun a b => by
        simp only [Submodule.coe_add, Pi.add_apply, Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Pi.smul_apply, Matrix.smul_mul, Matrix.trace_smul, RingHom.id_apply] }
  obtain ⟨T, hT⟩ := Det.finDet f
  refine ⟨T.card, fun j => (T.equivFin.symm j).1.1, fun j => (T.equivFin.symm j).1.2, ?_⟩
  intro z hzc hz _ htr
  have hzZ : z ∈ Z1 R := (mem_Z1_iff_cocycle _ _).2 ⟨hzc, fun g h => by rw [hR]; exact hz g h⟩
  have hall := hT ⟨z, hzZ⟩ fun s hs k =>
    htr s.1 ⟨T.equivFin ⟨s, hs⟩, by simp only [Equiv.symm_apply_apply]⟩ k
  refine Det.detG ρ (F.eps O (Qbar l)) F.G' z hn (Abelianization.commutator_subset_ker _) ?_ ?_ hI hz ?_
  · intro g hg
    have h1 : F.ε g = 1 := hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hχ, h1]
    simp
  · obtain ⟨g, hg⟩ := hε
    intro h
    apply hg
    have h1 := hχ g
    rw [h, MonoidHom.one_apply, Units.val_one, ← map_one (algebraMap ℚ_[l] (Qbar l))] at h1
    have h2 := (algebraMap ℚ_[l] (Qbar l)).injective h1
    exact Units.ext (Subtype.ext h2.symm)
  · intro g hg
    by_contra hne
    have ho : IsOpen {x : F.G₀ | (z x * W.mat ρ x).trace ≠ 0} :=
      isOpen_ne_fun (hzc.mul hm).matrix_trace continuous_const
    obtain ⟨σ, ⟨h1, h2⟩, h4⟩ := h3 _ ho ⟨g, hne, hg⟩
    have h5 : (z σ * W.mat ρ σ ^ 1).trace = 0 := hall ⟨σ, h2, h4⟩ 1
    rw [pow_one] at h5
    exact h1 h5
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem ad_eq {H K : Type} [Group H] [CommRing K] {n : ℕ} (ρ : H →* GL (Fin n) K) (g : H) (X : Matrix (Fin n) (Fin n) K) :
    Loc.adGL ρ g X = W.mat ρ g * X * W.mat ρ g⁻¹ := by
  change _ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)
  rw [map_inv]
  rfl

private theorem cont_sub {H K : Type} [Group H] [TopologicalSpace H] [ContinuousInv H] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} {a y : H → Matrix (Fin n) (Fin n) K} (ha : Continuous a) (hy : Continuous y)
    (X : Matrix (Fin n) (Fin n) K) : Continuous fun g => y g - (a g * X * a g⁻¹ - X) :=
  hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)

theorem UpperTheory.V.Th.core_of :
    Th.OrdVan2 → W.PhiAll → Th.Core := by
  intro hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo
  obtain ⟨h, hh⟩ := hN.arith
  obtain ⟨hD, -⟩ := Det.redB x ρ hN.rep
  have hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g
  have hI := (Ws.Eb.relKill B x ρ hfull hD).2
  obtain ⟨X₀, hpol, hext⟩ := Det.polNorm V.frame ρ P R z hR hz.2
  have heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1 := by
    obtain ⟨g, -, hg⟩ := h0.2.2
    refine ⟨g, fun e => hg ?_⟩
    have e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1 := e
    rw [W.GFrame.eps, MonoidHom.comp_apply, e', map_one]
  have hdet := regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3
  have hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
    intro v i j e
    by_cases hij : i = j
    · subst hij
      have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
      exact Det.epsDec (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 _).1 (by simpa using h1)) (left_eq_mul.1 e)
    · obtain ⟨g, hg, hf⟩ := hN.free v
      refine hf i j hij 1 one_pos ?_
      have e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g)) :=
        DFunLike.congr_fun V.hε _
      have e2 : cycZ L Ω l (Subtype.val g) = 1 := e1.symm.trans hg
      have e3 : cycBar L Ω l (Subtype.val g) = 1 := by rw [cycBar, MonoidHom.comp_apply, e2, map_one]
      have e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g) := DFunLike.congr_fun e g
      rw [e3, mul_one] at e4
      simp only [pow_one]
      exact e4
  have hc : Continuous fun g : V.frame.G₀ => W.mat ρ g := Units.continuous_val.comp hN.cont
  refine (hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet
    (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext
  · exact cont_sub hc (hz.1.comp continuous_subtype_val) X₀
  · have e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹ := by
      rw [← ad_eq, ← hR.ad]
      exact hz.2 _ _
    have e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]
    noncomm_ring
  · simp only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]
    simp
  · obtain ⟨a, X, ha⟩ := hzo.ord v
    refine ⟨a⁻¹, X - X₀, fun g => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := ha g
    have e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) =
        z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X) := by
      rw [ad_eq]
      have e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t) := fun _ => rfl
      simp only [Pa.dY, e1, map_inv]
      noncomm_ring
    rw [inv_inv, e]
    exact ⟨a1, a2, a3, a4⟩
end
