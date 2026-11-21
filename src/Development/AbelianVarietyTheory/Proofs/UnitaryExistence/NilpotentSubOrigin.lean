import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCompatOfGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)

theorem exists_sec_ne_zero {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] [IsProper G.hom] {L : LB G.left} (hL : L.IsLB)
    (hA : RelAmple G L) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (q : (Over.mk x0 ⊗ G).left) :
    ∃ k : ℕ, 0 < k ∧ ∃ F : LB.Sec (LPow G L k (Over.mk x0)), q ∈ nonzeroLocus F := by
  let π := (snd (Over.mk x0) G).left
  let f : (Over.mk x0 ⊗ G).left ⟶ Sp S := (fst (Over.mk x0) G).left
  have hp : IsPullback π f G.hom x0 := (IsPullback.of_hasPullback x0 G.hom).flip
  obtain ⟨N, hN, M, s, hcov, -⟩ := AmpleBaseChange.relAmple_of_isPullback hL hA hp ⊤ (isAffineOpen_top _)
  obtain ⟨h, hh⟩ : ∃ h : (Over.mk x0 ⊗ G).left ⟶ (f ⁻¹ᵁ ⊤).toScheme, h ≫ (f ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hy : ∀ y, (f ⁻¹ᵁ ⊤).ι (h y) = y := fun y => congrArg (fun g => g y) hh
  have le : ∀ j : Fin 1 → L.ι, (LPow G L N (Over.mk x0)).U j ≤
      h ⁻¹ᵁ (powOver (Over.mk f) (L.pull π) ⊤ N).U (fun _ _ => j 0) := fun j y hj =>
    Set.mem_iInter.2 fun _ => mem_pull.2 (by
      show π ((f ⁻¹ᵁ ⊤).ι (h y)) ∈ L.U (j 0)
      rw [hy]; exact Set.mem_iInter.1 hj 0)
  let a : ChartPull (LPow G L N (Over.mk x0)) (powOver (Over.mk f) (L.pull π) ⊤ N) h :=
    { idx := fun j _ _ => j 0
      le := le
      g := fun y j j' hj hj' => by
        refine (gm_linComb L (fun _ : Fin 1 => π) (fun _ => (N : ℤ)) (𝟙 _) y j j' hj hj').trans
          (Eq.trans ?_ (gm_linComb (L.pull π) (fun _ : Fin N => (f ⁻¹ᵁ ⊤).ι) (fun _ => 1) h y _ _
            (le j hj) (le j' hj')).symm)
        rw [Fin.prod_univ_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_one, zpow_natCast, hh]
        exact congrArg (· ^ N) (gm_pull_g L π (𝟙 _) y (fun _ => j 0) (fun _ => j' 0)
          (mem_pull.2 (Set.mem_iInter.1 hj 0)) (mem_pull.2 (Set.mem_iInter.1 hj' 0))).symm }
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show h q ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  refine ⟨N, hN, chartSec a (s i), (nonzeroLocus_chartSec a (s i) fun y _ _ => ?_).ge hi⟩
  obtain ⟨i, hi⟩ := exists_chart hL (π y)
  exact ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩

theorem val_stalk {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : W ⟶ Z) (r : Z ⟶ Y) {w : W} {J : (W ⟶ X) → L.ι} (hJ : Good L w J) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (val t r (κ w) fun ψ => J (κ ≫ ψ)) = val t (κ ≫ r) w J := by
  rw [val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]
  have h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k) := Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)
  exact Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans
    ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans (gm_val (κ ≫ r) w _ h _).symm))

theorem eq_one_of_pow {R : Type} [CommRing R] {r : R} {k : ℕ} (hk : IsUnit (k : R)) (hn : IsNilpotent (r - 1))
    (h : r ^ k = 1) : r = 1 := by
  have h1 : r - 1 ∣ (∑ i ∈ Finset.range k, r ^ i) - k := by
    have : (∑ i ∈ Finset.range k, r ^ i) - k = ∑ i ∈ Finset.range k, (r ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow r 1 i
  obtain ⟨c, hc⟩ := h1
  have hu : IsUnit (∑ i ∈ Finset.range k, r ^ i) := by
    rw [sub_eq_iff_eq_add.1 hc]
    exact ((Commute.all _ _).isNilpotent_mul_right hn).isUnit_add_right_of_commute hk (Commute.all _ _)
  have := geom_sum_mul r k
  rw [h, sub_self] at this
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d n : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}


variable (x0 d) in

abbrev tr (m n : ℕ) : jOG x0 d m n ⟶ jOG x0 d (m + 1) n :=
  homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m)






def cstHom {V : Type} [CommRing V] (y : Sp V) : V →+* (Sp V).presheaf.stalk y :=
  ((Sp V).presheaf.germ ⊤ y trivial).hom.comp (toΓ V)

theorem cst_eq {V : Type} [CommRing V] (y : Sp V) (a : V) : cst (𝟙 _) y a = cstHom y a := gs_eq (𝟙 _) y ⊤ trivial _


variable {G : FGLaw S d} {A : Germ.OAct (𝓞 E) G} {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)}
  {uvec : κ → Fin d → S} {e : ∀ m, FrTyG t x0 d x m} {ph1 ph2 : PS S 3 d} {sy : PS S 2 d} {ad : 𝓞 E → PS S 2 d}


end GlobalTheory.FrameCompatOfGerms
