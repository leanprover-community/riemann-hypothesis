import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtLatModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem htLat_le_omLat (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) : M.htLat N p ≤ M.omLat p := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨_, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, -, hj, -, hw⟩ e he
  refine Submodule.span_induction (p := fun e _ => w e ∈ regAt ξ p) ?_ ?_ ?_ ?_ he
  · rintro e ⟨v, hv, hev⟩
    obtain ⟨l, rfl⟩ := M₀.onto v hv
    have : e = j l := M.inj (Over.OverMorphism.ext (hev.trans (hj l).symm))
    rw [this, hw]
    exact ⟨_, rfl⟩
  · simp
  · intro a b _ _ ha hb
    simpa using add_mem ha hb
  · intro c a _ ha
    have : w (c • a) = (c : Ω) * w a := by
      rw [Subring.smul_def, map_smul, smul_eq_mul]
    rw [this]
    exact mul_mem c.2 ha

def triv (R : Type) [CommRing R] [IsDomain R] : BT.QFGroup R Unit where
  G := 𝟙_ _
  flat := inferInstanceAs (Flat (𝟙 _))
  quasiFinite := inferInstanceAs (LocallyQuasiFinite (𝟙 _))
  separated := inferInstanceAs (IsSeparated (𝟙 _))
  quasiCompact := inferInstanceAs (QuasiCompact (𝟙 _))
  finPres := inferInstanceAs (LocallyOfFinitePresentation (𝟙 _))
  pt := 1
  pt_inj _ _ _ _ _ := rfl
  pt_onto g hg := by
    refine ⟨(), IsLocalRing.closedPoint (FractionRing R), ?_⟩
    have h : ((1 : Unit →* (BT.genPt R ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))))) ()).left = (BT.genPt R).hom := by
      have := Over.w ((1 : Unit →* (BT.genPt R ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))))) ())
      simpa using this
    rw [h]
    apply PrimeSpectrum.ext
    refine Eq.trans ?_ (show g.asIdeal = ⊥ from hg).symm
    change Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal (FractionRing R)) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)]
  gen_reduced := by
    have : IsIso (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (IsIso (𝟙 _))
    have : IsReduced (BT.genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
    exact isReduced_of_isOpenImmersion (pullback.snd _ (BT.genPt R).hom)

theorem triv_torsion {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ)
    (h : ∀ (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x) ⟶ G), g ^ N = 1 → g = 1) :
    (triv R).IsTorsionAlong G x N (1 : Over.mk x ⟶ G).left := by
  have key : ∀ (Y : Over (Spec (CommRingCat.of R))) (y : Y ⟶ (triv R).G),
      y.left ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
    intro Y y
    have hy : y.left = Y.hom := (Category.comp_id _).symm.trans (Over.w y)
    have := MonObj.comp_one (M := G) (Over.homMk Y.hom rfl : Over.mk (Y.hom ≫ x) ⟶ Over.mk x)
    rw [hy]
    exact congrArg (fun q => q.left) this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Over.w (1 : Over.mk x ⟶ G)).trans (Category.id_comp _).symm
  · intro Y y z y₀ z₀ hy hz
    rw [key] at hy hz ⊢
    rw [Over.OverMorphism.ext hy, Over.OverMorphism.ext hz, _root_.mul_one]
  · intro Y y z _
    exact toUnit_unique _ _
  · intro Y g
    constructor
    · intro hg
      exact ⟨toUnit _, by rw [key, h Y g hg]⟩
    · rintro ⟨y, hy⟩
      rw [key] at hy
      rw [← Over.OverMorphism.ext hy, one_pow]






end GlobalTheory.CompanionTheory.Ar.HtLatModel
