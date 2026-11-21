import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqAtDetRootsOfCongruent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_fixing_seesaw_vacuum_definite_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac := by
  first | exact @GlobalTheory.VacFixTarget.exists_open_fix_vac_target | exact GlobalTheory.VacFixTarget.exists_open_fix_vac_target | (intros; apply GlobalTheory.VacFixTarget.exists_open_fix_vac_target <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.HeckeLevel

theorem add_mul_sub_one {R : Type} [CommRing R] (m c : ℕ) (w : R) :
    1 + ((m * c : ℕ) : R) * w - 1 = m • ((c : R) * w) := by
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem exists_level : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  intro D ν hν
  obtain ⟨N₀, hN₀, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν.1
  refine ⟨N₀, hN₀, ?_⟩
  rintro N ⟨c, rfl⟩ u hu ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  have key : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z : Lev.EAf D) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E → z ∈ intAE D :=
    fun z hz => (GlobalTheory.IdemSupport.mem_intAE_iff z).2 hz
  have hint : ∀ (a : AE D) (v : Lev.EAf D), v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
      toEAf D a = 1 + ((N₀ * c : ℕ) : Lev.EAf D) * v → finPart D a ∈ intAE D := by
    intro a v hv ha
    refine key _ ?_
    change toEAf D a ∈ _
    rw [ha]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) hv)
  refine hker u ⟨hu, hint _ w hw e, hint _ w' hw' e'⟩
    ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm ((c : Lev.EAf D) * w), key _ ?_, ?_⟩
  · rw [AlgEquiv.apply_symm_apply]
    exact mul_mem (natCast_mem _ _) hw
  · apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    rw [map_sub, map_one, map_nsmul, AlgEquiv.apply_symm_apply]
    have e2 : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (u : AE D)) : Lev.EAf D) =
      1 + ((N₀ * c : ℕ) : Lev.EAf D) * w := e
    rw [e2]
    exact add_mul_sub_one N₀ c w

end GlobalTheory.HeckeLevel
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_unitaryHeckeCharacter_trivial_congruence : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  atlas_forward_decl GlobalTheory.HeckeLevel.exists_level
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.FrameCongOpen

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def congInt (N : ℕ) : Subgroup (GL (Fin n) (Formalism.L2.Herm.intAf F E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n)
    (Ideal.Quotient.mk (Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)}))).ker

theorem mem_congInt_span {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, z.1 a b - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b ∈
      Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)} := by
  rw [congInt, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [← Ideal.Quotient.eq]
  change Ideal.Quotient.mk _ (z.1 a b) = (1 : Matrix (Fin n) (Fin n) _) a b ↔ _
  simp only [Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem mem_congInt {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  have hone : ∀ a b, (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b : Formalism.L2.Herm.intAf F E) :
      E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) a b := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> rfl
  rw [mem_congInt_span]
  refine forall₂_congr fun a b => ?_
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    rw [← hone, ← AddSubgroupClass.coe_sub, ← hc, Subring.coe_mul, Subring.coe_natCast, mul_comm]
  · rintro ⟨w, hw, e⟩
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub, hone, e, mul_comm]

theorem mem_cong (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ)
    (h1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h3 : ∀ i j, ∃ z ∈ Formalism.L2.Herm.intAf F E,
      (β⁻¹ * x * β).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (N : E ⊗[F] Formalism.L2.Herm.Af F) * z) :
    x ∈ (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  have hx : x = β * (β⁻¹ * x * β) * β⁻¹ := by group
  generalize β⁻¹ * x * β = m at h1 h2 h3 hx
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      A.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
  let y : GL (Fin n) (Formalism.L2.Herm.intAf F E) :=
    ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩,
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.mul_inv),
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.inv_mul)⟩
  have hy : frGL β y = x := by
    have : intGL F E n y = m := Units.ext rfl
    rw [hx, ← this]
    rfl
  exact ⟨y, (mem_congInt y).2 fun i j => h3 i j, hy⟩

theorem eventually_cong_mat (β : GL (Fin n) (E ⊗[F] Af F)) (N : ℕ) (hN : 0 < N) {X : Type} [TopologicalSpace X]
    {x₀ : X} {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) ∈
      (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈
      GlobalTheory.Mass.intTens F E := fun i j => by
    simp only [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)
  have e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ i j,
      algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    have hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage hc).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e1, e2, e3] with κ h1 h2 h3
  refine mem_cong β _ N ?_ ?_ ?_
  · rw [hs]; exact h1
  · rw [hs, ← map_inv]; exact h2
  · intro i j
    refine ⟨_, h3 i j, ?_⟩
    have hN' : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j =
        (N : ℕ) * (algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)) := by
      rw [← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul,
        mul_inv_cancel₀ hN', map_one, one_mul]
    have := congrArg s e
    rw [map_mul, map_natCast, map_sub] at this
    rw [hs]
    refine Eq.trans ?_ this
    congr 1
    simp only [Matrix.one_apply]; split_ifs <;> simp

def congFr (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  (congInt (F := F) (E := E) (n := n) N).map (frGL β)

theorem mem_congFr {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N : ℕ} (hx : x ∈ congFr β N) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf F E), frGL β z = x ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  obtain ⟨z, hz, e⟩ := Subgroup.mem_map.1 hx
  exact ⟨z, e, (mem_congInt z).1 hz⟩

end General

theorem exists_open_cong : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ κ ∈ U, ∃ z : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.frGL β z = Lev.finE V κ ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w := by
  intro D V β N hN
  refine ⟨(congFr β N).comap (Formalism.IndefR.Lev.finE V),
    ?_, fun κ hκ => ?_⟩
  · haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hf : Continuous (finHom V) :=
      (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    exact eventually_cong_mat β N hN hf (map_one _)
  · exact mem_congFr (Subgroup.mem_comap.1 hκ)

end GlobalTheory.FrameCongOpen

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_frame_congruence_unitaryAdelic : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ κ ∈ U, ∃ z : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.frGL β z = Lev.finE V κ ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w := by
  atlas_forward_decl GlobalTheory.FrameCongOpen.exists_open_cong
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.UnitCharCong

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

theorem hom_sum {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ι → R) (s : Finset ι) :
    f (∑ i ∈ s, p i) = ∑ i ∈ s, f (p i) := map_sum f p s

theorem hom_shift {R κ : Type} [CommRing R] [CommRing κ] (f : R →+* κ) {a b z u u' : R} (h0 : f a * f b = 0)
    (hu' : u' = u + a * (b * z)) : f u' = f u := by
  rw [hu', map_add, map_mul, map_mul, ← mul_assoc, h0, zero_mul, add_zero]

theorem hom_natCast {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) : f n = n := map_natCast f n

theorem toEAf_surj (z : EAf D) : ∃ w : AE D, infPart D w = 0 ∧ toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _, RingHom.map_zero _⟩
  | tmul b α =>
    refine ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, ?_, rfl⟩
    change (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] b = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, by rw [RingHom.map_add, ha, hb, add_zero], RingHom.map_add _ _ _⟩

theorem finPart_eq_of_toEAf {a b : AE D} (h : toEAf D a = toEAf D b) : finPart D a = finPart D b :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

theorem eq_of_parts {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : toEAf D a = toEAf D b) : a = b := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, h1, sub_self]
  · rw [RingHom.map_sub, finPart_eq_of_toEAf h2, sub_self]

theorem exists_unit {u v : EAf D} (huv : u * v = 1) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = u ∧ toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = v := by
  obtain ⟨g₁, a₁, b₁⟩ := toEAf_surj (1 : EAf D)
  obtain ⟨g, a₂, b₂⟩ := toEAf_surj u
  obtain ⟨g', a₃, b₃⟩ := toEAf_surj v
  have w₁ : infPart D (1 - g₁) = 1 := by rw [RingHom.map_sub, a₁, RingHom.map_one, sub_zero]
  have w₀ : toEAf D (1 - g₁) = 0 := by rw [RingHom.map_sub, b₁, RingHom.map_one, sub_self]
  have h : (1 - g₁ + g) * (1 - g₁ + g') = 1 := eq_of_parts
    (by simp only [RingHom.map_mul, RingHom.map_add, w₁, a₂, a₃, RingHom.map_one, add_zero, mul_one])
    (by simp only [RingHom.map_mul, RingHom.map_add, w₀, b₂, b₃, RingHom.map_one, zero_add, huv])
  refine ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, ?_, ?_, ?_⟩
  · change infPart D (1 - g₁ + g) = 1
    rw [RingHom.map_add, w₁, a₂, add_zero]
  · change toEAf D (1 - g₁ + g) = u
    rw [RingHom.map_add, w₀, b₂, zero_add]
  · change toEAf D (1 - g₁ + g') = v
    rw [RingHom.map_add, w₀, b₃, zero_add]

theorem res_idem_off {a : AE D} {P Q : Pl D.host.E} (ha : Formalism.L2.NTheta.IsIdemAt a P) (hQ : Q ≠ P)
    (h : toEAf D a ∈ OO) : resS D.host.F Q ⟨toEAf D a, h⟩ = 0 := by
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra hc
    push Not at hc
    exact hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isMaximal.ne_top hc))
  have hx0 : x ≠ 0 := fun h0 => hxP (h0 ▸ P.asIdeal.zero_mem)
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hmem : finPart D (a * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hxP ((ha.2 x hx0).2 hn)
  have hs := GlobalTheory.IdemRes.toEAf_mem_of_finPart hmem
  have e1 : (⟨toEAf D a, h⟩ : OO) = ⟨_, hs⟩ * oToS D.host.F D.host.E x := Subtype.ext (by
    change toEAf D a = toEAf D (a * incA D ((x : D.host.E)⁻¹)) * eToEAf D (x : D.host.E)
    have h2 : toEAf D (incA D ((x : D.host.E)⁻¹)) = eToEAf D ((x : D.host.E)⁻¹) := rfl
    rw [RingHom.map_mul, h2, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hx0', RingHom.map_one, mul_one])
  rw [e1, RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hxQ, mul_zero]

theorem res_off {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (h : toEAf D e ∈ OO) {Q : Pl D.host.E}
    (hQ : Q ∉ S) : resS D.host.F Q ⟨toEAf D e, h⟩ = 0 := by
  obtain ⟨⟨es, hes, hs⟩, -⟩ := he
  have hi : ∀ P ∈ S, toEAf D (es P) ∈ OO := fun P hP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (hes P hP)).1
  have e1 : (⟨toEAf D e, h⟩ : OO) = ∑ P ∈ S.attach, ⟨toEAf D (es P.1), hi P.1 P.2⟩ := Subtype.ext (by
    refine Eq.trans ?_ (hom_sum (OO).subtype _ _).symm
    change toEAf D e = ∑ P ∈ S.attach, toEAf D (es P.1)
    rw [hs, hom_sum, Finset.sum_attach S fun P => toEAf D (es P)])
  rw [e1, hom_sum]
  exact Finset.sum_eq_zero fun P _ => res_idem_off (hes P.1 P.2) (fun hh => hQ (by rw [hh]; exact P.2)) _

theorem isUnit_add {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (h : toEAf D e ∈ OO) {c : ℕ}
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {u u' z : OO} (hu : IsUnit u)
    (hu' : u' = u + ⟨toEAf D e, h⟩ * ((c : OO) * z)) : IsUnit u' := by
  refine isUnit_of_resS_ne_zero D.sp.cm _ fun Q => ?_
  have := Q.isPrime
  have h0 : resS D.host.F Q ⟨toEAf D e, h⟩ * resS D.host.F Q (c : OO) = 0 := by
    by_cases hQ : Q ∈ S
    · have h1 : resS D.host.F Q (c : OO) = Ideal.Quotient.mk Q.asIdeal ((c : ℕ) : 𝓞 D.host.E) := by
        rw [hom_natCast (Ideal.Quotient.mk Q.asIdeal), ← hom_natCast (resS D.host.F Q)]
      rw [h1, Ideal.Quotient.eq_zero_iff_mem.2 (hc Q hQ), mul_zero]
    · rw [res_off he h hQ, zero_mul]
  exact (hom_shift (resS D.host.F Q) h0 hu').symm ▸ (hu.map (resS D.host.F Q)).ne_zero

theorem det_cong {R : Type} [CommRing R] {k : ℕ} {A B : Matrix (Fin k) (Fin k) R} {c : R}
    (h : ∀ i j, ∃ z, B i j = A i j + c * z) : ∃ z, B.det = A.det + c * z := by
  have e : (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix B = (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix A := by
    ext i j
    obtain ⟨z, hz⟩ := h i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hz, RingHom.map_add, RingHom.map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c), zero_mul, add_zero]
  have e2 : Ideal.Quotient.mk (Ideal.span {c}) B.det = Ideal.Quotient.mk (Ideal.span {c}) A.det := by
    rw [RingHom.map_det, RingHom.map_det, e]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e2)
  exact ⟨z, by linear_combination -hz⟩

theorem det_cong_int {k : ℕ} {N N' Z : Matrix (Fin k) (Fin k) (EAf D)} (hN : IsIntM N) (hZ : IsIntM Z) {c : ℕ}
    (h : ∀ i j, N' i j = N i j + c * Z i j) : ∃ hd : N.det ∈ OO, ∃ hd' : N'.det ∈ OO, ∃ z : OO,
      (⟨N'.det, hd'⟩ : OO) = ⟨N.det, hd⟩ + c * z := by
  have hN' : IsIntM N' := fun i j => by
    rw [h]
    exact add_mem (hN i j) (mul_mem (natCast_mem _ _) (hZ i j))
  let A : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N i j, hN i j⟩
  let B : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N' i j, hN' i j⟩
  have eA : N.det = ((A.det : OO) : EAf D) := by
    have := RingHom.map_det (OO).subtype A
    rw [show N = (OO).subtype.mapMatrix A from rfl]
    exact this.symm
  have eB : N'.det = ((B.det : OO) : EAf D) := by
    have := RingHom.map_det (OO).subtype B
    rw [show N' = (OO).subtype.mapMatrix B from rfl]
    exact this.symm
  obtain ⟨z, hz⟩ := det_cong (A := A) (B := B) (c := (c : OO)) fun i j => ⟨⟨Z i j, hZ i j⟩, Subtype.ext (h i j)⟩
  refine ⟨eA ▸ A.det.2, eB ▸ B.det.2, z, Subtype.ext ?_⟩
  have := congrArg Subtype.val hz
  simpa [eA, eB] using this

theorem coe_nat {R : Type} [CommRing R] (A : Subring R) (n : ℕ) : (((n : A)) : R) = n := map_natCast A.subtype n

theorem hom_nsmul {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) (a : R) : f (n • a) = n • f a :=
  map_nsmul f n a

theorem ring_id {R : Type} [CommRing R] {t t' ti ε d d' n c z : R} (a : t = 1 - ε + ε * d) (b : t' = 1 - ε + ε * d')
    (hz : d' = d + n * c * z) (hm : t * ti = 1) : t' * ti - 1 = n * (ε * (c * z) * ti) := by
  subst a b hz
  linear_combination hm

theorem ring_id' {R : Type} [CommRing R] {ε d d' c z : R} (hz : d' = d + c * z) :
    1 - ε + ε * d' = (1 - ε + ε * d) + ε * (c * z) := by
  subst hz
  ring

theorem toEAf_mem {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) : toEAf D e ∈ OO :=
  GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _
    (by rw [← RingHom.map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]))

theorem exists_isUnitDet {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {c : ℕ}
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {k : ℕ} {N N' Z : Matrix (Fin k) (Fin k) (EAf D)}
    (hN : IsIntM N) (hZ : IsIntM Z) (h : ∀ i j, N' i j = N i j + c * Z i j)
    (hx : ∃ x, IsUnitDet e N x) : ∃ x, IsUnitDet e N' x := by
  obtain ⟨x, h1, h2, h3⟩ := hx
  have hE := toEAf_mem he
  obtain ⟨hd, hd', z, hz⟩ := det_cong_int hN hZ h
  have hzv : N'.det = N.det + (c : EAf D) * (z : EAf D) := by
    have := congrArg Subtype.val hz
    rw [← coe_nat (OO) c]
    exact this
  have hu : toEAf D (x : AE D) ∈ OO := by
    rw [h2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd)
  have hu' : 1 - toEAf D e + toEAf D e * N'.det ∈ OO := add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd')
  have hxx : (⟨_, hu⟩ : OO) * ⟨_, h3⟩ = 1 := Subtype.ext (by
    change toEAf D (x : AE D) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  have hU : IsUnit (⟨_, hu⟩ : OO) := IsUnit.of_mul_eq_one _ hxx
  have hU' : IsUnit (⟨_, hu'⟩ : OO) := isUnit_add he hE hc hU (z := z) (Subtype.ext (by
    change 1 - toEAf D e + toEAf D e * N'.det = toEAf D (x : AE D) + toEAf D e * (((c : OO) : EAf D) * (z : EAf D))
    rw [coe_nat, h2]
    exact ring_id' hzv))
  obtain ⟨w, hw⟩ := hU'.exists_right_inv
  obtain ⟨x', a, b, d⟩ := exists_unit (u := 1 - toEAf D e + toEAf D e * N'.det) (v := (w : EAf D)) (congrArg Subtype.val hw)
  exact ⟨x', a, b, by rw [d]; exact w.2⟩

set_option maxHeartbeats 2000000 in

theorem nu_eq {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {n c : ℕ}
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1) {k : ℕ}
    {N N' Z : Matrix (Fin k) (Fin k) (EAf D)} (hN : IsIntM N) (hZ : IsIntM Z)
    (h : ∀ i j, N' i j = N i j + ((n * c : ℕ) : EAf D) * Z i j) {x x' : (AE D)ˣ} (hx : IsUnitDet e N x)
    (hx' : IsUnitDet e N' x') : ν x = ν x' := by
  obtain ⟨a1, a2, a3⟩ := hx
  obtain ⟨b1, b2, b3⟩ := hx'
  have hE := toEAf_mem he
  obtain ⟨hd, hd', z, hz⟩ := det_cong_int hN hZ h
  have hzv : N'.det = N.det + (n : EAf D) * (c : EAf D) * (z : EAf D) := by
    have := congrArg Subtype.val hz
    rw [← Nat.cast_mul, ← coe_nat (OO) (n * c)]
    exact this
  have hX : toEAf D (x : AE D) ∈ OO := by
    rw [a2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd)
  have hX' : toEAf D (x' : AE D) ∈ OO := by
    rw [b2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd')
  have hm : toEAf D (x : AE D) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  have hinv : infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (infPart D) (Units.mul_inv x)
    rwa [RingHom.map_mul, a1, one_mul, RingHom.map_one] at this
  have hinv' : ((x' * x⁻¹ : (AE D)ˣ) : AE D) = (x' : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) := rfl
  have hinv2 : (((x' * x⁻¹)⁻¹ : (AE D)ˣ) : AE D) = (x : AE D) * ((x'⁻¹ : (AE D)ˣ) : AE D) := by
    rw [_root_.mul_inv_rev, inv_inv]
    rfl
  have hr : Formalism.L2.Pj.FinUnit (x' * x⁻¹) := by
    refine ⟨?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_⟩
    · rw [hinv', RingHom.map_mul, b1, hinv, one_mul]
    · rw [hinv', RingHom.map_mul]
      exact mul_mem hX' a3
    · rw [hinv2, RingHom.map_mul]
      exact mul_mem hX b3
  obtain ⟨w, -, hw⟩ := toEAf_surj (toEAf D e * ((c : EAf D) * (z : EAf D)) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D))
  have hwI : toEAf D w ∈ OO := by
    rw [hw]
    exact mul_mem (mul_mem hE (mul_mem (natCast_mem _ _) z.2)) a3
  have key : finPart D ((x' * x⁻¹ : (AE D)ˣ) : AE D) - 1 = n • finPart D w := by
    have e1 : finPart D (((x' * x⁻¹ : (AE D)ˣ) : AE D) - 1) = finPart D (n • w) :=
      finPart_eq_of_toEAf (by
        rw [RingHom.map_sub, RingHom.map_one, hinv', RingHom.map_mul, hom_nsmul, hw, nsmul_eq_mul]
        exact ring_id a2 b2 hzv hm)
    rw [RingHom.map_sub, RingHom.map_one, hom_nsmul] at e1
    exact e1
  have h1 := hl _ hr ⟨_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hwI, key⟩
  rw [map_mul, map_inv] at h1
  exact (mul_inv_eq_one.1 h1).symm

end

set_option maxHeartbeats 2000000 in

theorem unitChar_eq_of_natCong : ∀ (D : D7) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ N : ℕ, 0 < N → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ {k : ℕ} (P Q : Matrix (Fin k) (Fin k) (Lev.EAf D)), IsIntM (D := D) P → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Q a b - P a b = (N : Lev.EAf D) * w) → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e Q = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e P := by
  intro D ν e Sf he N _ hSf hν k P Q hP hQ
  choose Z hZ hZe using hQ
  have hZint : IsIntM (D := D) (fun a b => Z a b : Matrix (Fin k) (Fin k) (Lev.EAf D)) := fun a b => hZ a b
  have h : ∀ i j, Q i j = P i j + (N : Lev.EAf D) * Z i j := fun i j => eq_add_of_sub_eq' (hZe i j)
  have hQint : IsIntM (D := D) Q := fun i j => by
    rw [h]
    exact add_mem (hP i j) (mul_mem (natCast_mem _ _) (hZ i j))
  have hZn : IsIntM (D := D) (-(fun a b => Z a b : Matrix (Fin k) (Fin k) (Lev.EAf D))) := fun a b => neg_mem (hZ a b)
  have h' : ∀ i j, P i j = Q i j + (N : Lev.EAf D) * (-(fun a b => Z a b : Matrix (Fin k) (Fin k) (Lev.EAf D))) i j :=
    fun i j => by
      change P i j = Q i j + (N : Lev.EAf D) * (-(Z i j))
      rw [h, mul_neg, add_neg_cancel_right]
  have hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → ν x = 1 := by
    rintro x ⟨h1, -, h3⟩ ⟨y, hy, hxy⟩
    obtain ⟨a, -, ha⟩ := GlobalTheory.UnitCharCong.toEAf_surj (D := D) (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E y)
    have hfa : finPart D a = y := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective ha
    have haI : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.IdemRes.toEAf_mem_of_finPart (hfa ▸ hy)
    have hvI : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.IdemRes.toEAf_mem_of_finPart h3
    have hu : toEAf D (x : AE D) = 1 + (N : Lev.EAf D) * toEAf D a := by
      have := congrArg (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E) hxy
      rw [map_sub, map_one, map_nsmul, nsmul_eq_mul, ← ha] at this
      change toEAf D (x : AE D) - 1 = (N : Lev.EAf D) * toEAf D a at this
      linear_combination this
    have hm : toEAf D (x : AE D) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
      rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
    refine hν x h1 ⟨_, haI, hu⟩ ⟨-(toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D a), neg_mem (mul_mem hvI haI), ?_⟩
    linear_combination hm - toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * hu
  have f := fun hx => GlobalTheory.UnitCharCong.exists_isUnitDet he (c := N) hSf hP hZint h hx
  have g := fun hx => GlobalTheory.UnitCharCong.exists_isUnitDet he (c := N) hSf hQint hZn h' hx
  have h1 : ∀ i j, Q i j = P i j + ((N * 1 : ℕ) : Lev.EAf D) * (fun a b => Z a b : Matrix (Fin k) (Fin k) (Lev.EAf D)) i j :=
    fun i j => by rw [Nat.mul_one]; exact h i j
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar
  by_cases hx : ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e P x
  · rw [dif_pos (f hx), dif_pos hx, GlobalTheory.UnitCharCong.nu_eq he (n := N) (c := 1) hl hP hZint h1 hx.choose_spec (f hx).choose_spec]
  · rw [dif_neg (fun h => hx (g h)), dif_neg hx]

end GlobalTheory.UnitCharCong

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdFstInv

theorem mul_sub_mem {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (Z : Matrix (Fin b) (Fin b) R)
    (hZ : ∀ i j, ∃ w ∈ O, Z i j - (1 : Matrix (Fin b) (Fin b) R) i j = c * w)
    (Y : Matrix (Fin b) (Fin a) R) (hY : ∀ i j, Y i j ∈ O) (i : Fin b) (j : Fin a) :
    ∃ w ∈ O, (Z * Y) i j - Y i j = c * w := by
  choose w hwO hw using hZ
  refine ⟨∑ k, w i k * Y k j, O.sum_mem fun k _ => O.mul_mem (hwO i k) (hY k j), ?_⟩
  have hsplit : (Z * Y) i j - Y i j = ∑ k, (Z i k - (1 : Matrix (Fin b) (Fin b) R) i k) * Y k j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.one_mul]
  rw [hsplit, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hw i k, mul_assoc]

theorem mem_iff {R : Type} [CommRing R] (O : Subring R) (J : Ideal O) (N : ℕ) (hN : (N : O) ∈ J) {p q w : R}
    (hp : p ∈ O) (hw : w ∈ O) (h : q - p = (N : R) * w) :
    (∃ h : q ∈ O, (⟨q, h⟩ : O) ∈ J) ↔ ∃ h : p ∈ O, (⟨p, h⟩ : O) ∈ J := by
  have hq : q ∈ O := by
    have e : q = p + (N : R) * w := by linear_combination h
    rw [e]
    exact O.add_mem hp (O.mul_mem (natCast_mem O N) hw)
  have key : (⟨q, hq⟩ : O) = ⟨p, hp⟩ + (N : O) * ⟨w, hw⟩ := by
    apply Subtype.ext
    show q = p + ((N : O) : R) * w
    rw [show ((N : O) : R) = (N : R) from map_natCast O.subtype N]
    linear_combination h
  have hNw : (N : O) * ⟨w, hw⟩ ∈ J := J.mul_mem_right _ hN
  constructor
  · rintro ⟨_, hJ⟩
    refine ⟨hp, ?_⟩
    rw [key] at hJ
    exact (J.add_mem_iff_left hNw).1 hJ
  · rintro ⟨_, hJ⟩
    refine ⟨hq, ?_⟩
    rw [key]
    exact J.add_mem hJ hNw

theorem fixed_mul {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : Matrix (Fin b) (Fin b) R) (x : Matrix (Fin b) (Fin a) R)
    (H : ∀ i j, e * x i j = x i j) (i : Fin b) (j : Fin a) : e * (M * x) i j = (M * x) i j := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, H k j]

theorem fixed_iff {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : GL (Fin b) R) (P : Matrix (Fin a) (Fin a) R) (hP : P = 1)
    (x : Matrix (Fin b) (Fin a) R) :
    (∀ i j, e * (M.val * x * P) i j = (M.val * x * P) i j) ↔ ∀ i j, e * x i j = x i j := by
  subst hP
  simp only [Matrix.mul_one]
  constructor
  · intro h i j
    have hx : x = (M⁻¹).val * (M.val * x) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [hx]
    exact fixed_mul e _ _ h i j
  · intro h i j
    exact fixed_mul e _ _ h i j

variable {D : D7}

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V)⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [inv_one, map_one, Units.val_one]

theorem actO_neg_one (A WW : HSp D) (κ : GA D WW) (x : WO A WW) :
    actO (GlobalTheory.Grid.neg A) WW 1 κ x = actO A WW 1 κ x := by
  unfold actO
  rw [mt_one, mt_one]

theorem isHalf_iff (A WW : HSp D) (κ : GA D WW) (e : AE D) (x : WO A WW) :
    IsHalf e (actO A WW 1 κ x) ↔ IsHalf e x := by
  unfold IsHalf actO
  exact fixed_iff e (matHom WW κ) _ (mt_one A) x

theorem frMapO_eq {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) =
      ((intGL D.host.F D.host.E _ z⁻¹)⁻¹).val * frMapO A WW βA βW x *
        (intGL D.host.F D.host.E _ (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))).val := by
  have h1 := GlobalTheory.FrameRed.frMapO_actO (βS := βA) (βT := βW) (g := (1 : GA D A)) (h := κ⁻¹)
    (y := 1) (z := z⁻¹) (by rw [map_one, map_one]) (by rw [map_inv, map_inv, hz]) x
  rw [inv_one, inv_inv] at h1
  exact h1
set_option maxHeartbeats 1600000 in

theorem frMapO_eq' {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) = (intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x := by
  rw [frMapO_eq βA hz x, map_inv (intGL D.host.F D.host.E WW.rank), inv_inv,
    map_one (intGL D.host.F D.host.E A.rank), Units.val_one, Matrix.mul_one]

theorem topL_int {b a : ℕ} (k : ℕ) {Y : Matrix (Fin b) (Fin a) (Lev.EAf D)} (hY : IsIntM (D := D) Y) :
    IsIntM (D := D) (topL k Y) := by
  intro i j
  unfold topL
  split_ifs with hij
  · exact hY _ _
  · exact zero_mem _

theorem topL_sub {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (k : ℕ) {Y Y' : Matrix (Fin b) (Fin a) R}
    (h : ∀ i j, ∃ w ∈ O, Y' i j - Y i j = c * w) (i j : Fin k) :
    ∃ w ∈ O, topL k Y' i j - topL k Y i j = c * w := by
  unfold topL
  split_ifs with hij
  · exact h _ _
  · exact ⟨0, O.zero_mem, by rw [sub_self, mul_zero]⟩
set_option maxHeartbeats 1600000 in

theorem stdFst_actO : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  intro D A WW ν e Sf hSf I βA βW N hN hNI hNS hν κ z hz hz1 x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [actO_neg_one, isHalf_iff, frMapO_eq' βA hz x]
  have hInt : IsIntM (D := D) ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) ↔
      IsIntM (D := D) (frMapO A WW βA βW x) := by
    have h2 := GlobalTheory.FrameRed.isIntM_iff (D := D) z⁻¹
      (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (frMapO A WW βA βW x)
    rwa [map_inv (intGL D.host.F D.host.E WW.rank), inv_inv, map_one (intGL D.host.F D.host.E A.rank),
      Units.val_one, Matrix.mul_one] at h2
  by_cases hM : IsIntM (D := D) (frMapO A WW βA βW x)
  · have hc : ∀ i j, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
        ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j - frMapO A WW βA βW x i j =
          (N : Lev.EAf D) * w :=
      mul_sub_mem (Formalism.L2.Herm.intAf D.host.F D.host.E) (N : Lev.EAf D) (intGL D.host.F D.host.E _ z).val hz1 _ hM
    have hNJ : ((N : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F I := by
      rw [← map_natCast (Formalism.L2.DIV.oToS D.host.F D.host.E) N]
      exact Ideal.mem_map_of_mem _ hNI
    have hId : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j) ↔
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW x i j) := fun i j => by
      obtain ⟨w, hw, hq⟩ := hc i j
      exact GlobalTheory.StdFstInv.mem_iff _ _ N hNJ (hM i j) hw hq
    have hU := GlobalTheory.UnitCharCong.unitChar_eq_of_natCong D ν e Sf hSf N hN hNS hν _ _ (topL_int A.rank hM)
      (topL_sub _ _ A.rank hc)
    rw [hU]
    have hcond := and_congr (Iff.rfl (a := IsHalf e x)) (and_congr hInt
      (forall_congr' fun (i : Fin WW.rank) => forall_congr' fun (j : Fin A.rank) =>
        imp_congr (Iff.rfl (a := A.rank ≤ (i : ℕ))) (hId i j)))
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hcond.1 h1) h2
    · exact absurd (hcond.2 h2) h1
    · rfl
  · rw [if_neg (fun h => hM (hInt.1 h.2.1)), if_neg (fun h => hM h.2.1)]

end GlobalTheory.StdFstInv

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirst_invariant_congruenceOne : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  atlas_forward_decl GlobalTheory.StdFstInv.stdFst_actO
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.RowTest

theorem IsBottomTri.exists_open_fix_f : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac →
      X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  have h := hX.is
  have hom := h.weil t
  have hT2 : IsHeckeChar D ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) :=
    hom.hecT
  have hx : ∀ x, ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) x =
      (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) x)⁻¹ := fun x => by
    rw [MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
  have hνH : IsHeckeChar D ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) :=
    ⟨hT2.1.inv.congr fun x => (hx x).symm, fun x => by rw [hx, hT2.2, inv_one]⟩
  obtain ⟨N₀, hN₀, hN₀'⟩ := GlobalTheory.T.exists_level_unitaryHeckeCharacter_trivial_congruence D _ hνH
  have hI : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  set N : ℕ := N₀ * Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal with hNdef
  have hNpos : 0 < N := by
    refine Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hN₀.ne' ?_) (Finset.prod_ne_zero_iff.2 fun w _ => ?_))
    · exact fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    · exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hNI : ((N : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t := by
    rw [hNdef, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))
  have hNw : ∀ w ∈ locPl G t, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => Ideal.absNorm w.asIdeal) hw
    rw [hNdef, hc, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))
  have hNdiv : N₀ ∣ N := ⟨Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal, by rw [hNdef, mul_assoc]⟩
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.exists_open_frame_congruence_unitaryAdelic D WW X.rW.β N hNpos
  refine ⟨U, hUo, fun κ hκ _ hvac => ?_⟩
  obtain ⟨z, hz, hzc⟩ := hU κ hκ
  have hst : Lev.finE WW κ ∈ Formalism.L2.DIV.St X.rW.β := ⟨z, hz⟩
  have hinv := GlobalTheory.T.standardPairFirst_invariant_congruenceOne D A WW _ (X.e t) (locPl G t) (h.idem t) (X.ideal (locPl G) t) X.rA.β X.rW.β N hNpos hNI hNw
    (hN₀' N hNdiv) κ z hz hzc
  have hsdA := isSelfDualC_neg' h.rigA.1
  have hsdW := h.rigW.1
  have hsg : ∀ f, (X.ω t).toSgn true (1, κ) f = X.ω t (1, κ) f := fun f => by
    simp [GlobalTheory.Grid.WRep.toSgn]
  have key := GlobalTheory.ExportSeries.DualType.om_theta_move hom
    (fun Tm hT Ψ hΨ => GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ h.isVac.1 _ WW _ _ hsdA hsdW _
      (GlobalTheory.PlaceDatum.idemSum_mul_self (h.idem t)) (GlobalTheory.PlaceDatum.infPart_idemSum (h.idem t)) _ h.isVac.2.theta Tm hT Ψ hΨ)
    (h.fst t) (h.fst t) (g := 1) (h := κ)
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ WW _ _ _ _ hsdA hsdW h.rigA.2.1 h.rigW.2.1 1 κ (by rw [map_one]; exact one_mem _) hst)
    one_ne_zero (c' := 1) (by rw [one_smul, hsg]; exact hvac) (fun x => by rw [one_mul, hinv x])
  rw [hsg, one_mul, one_smul] at key
  exact key

end GlobalTheory.RowTest

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_exists_open_fixes_finiteVector : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac →
      X.ω t (1, κ) (X.f t) = X.f t := by
  atlas_forward_decl GlobalTheory.RowTest.IsBottomTri.exists_open_fix_f
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.BottomLevel

theorem fin_vec_fix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U₁, h₁, hU₁⟩ := GlobalTheory.T.exists_open_fixing_seesaw_vacuum_definite_bottom hX t
  obtain ⟨U₂, h₂, hU₂⟩ := GlobalTheory.T.definiteBottom_exists_open_fixes_finiteVector hX t
  exact ⟨U₁ ⊓ U₂, h₁.inter h₂, fun κ hκ hf => hU₂ κ hκ.2 hf (hU₁ κ hκ.1 hf)⟩

theorem rightTranslate_level : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (J : Subgroup (GA D WW)) (M₂ : IntermediateField ℚ ℂ), IsOpen (J : Set (GA D WW)) ∧ FiniteDimensional ℚ M₂ ∧
      ∀ t, ∀ κ ∈ J, κ ∈ GfC WW → ∃ ℓ ∈ M₂, ∀ P x, X.I W.ψ W.θ t P (x * κ) = ℓ * X.I W.ψ W.θ t P x := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX
  have hψ := hX.is.isVac.1
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hf : ∀ t, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) := fun t =>
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hX.is.fst t) hX.is.isVac.2.theta
  choose U hUo hU using fin_vec_fix hX
  refine ⟨⨅ t, U t, ⊥, ?_, inferInstance, fun t κ hκ hκf => ⟨1, one_mem _, fun P x => ?_⟩⟩
  · rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite fun t => hUo t
  · have hfix := hU t κ (Subgroup.mem_iInf.1 hκ t) hκf
    have hW := hX.is.weil t
    have hpt := GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW W.θ hθ 1 (one_mem _) κ hκf
      (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P (hf t)
    have e1 : ∀ g, (X.ω t).toSgn true (1, κ) g = X.ω t (1, κ) g := by
      intro g; simp [GlobalTheory.Grid.WRep.toSgn]
    rw [one_mul]
    unfold Tri.I Tri.ker thetaKO
    congr 1
    funext g
    have hm : ((g, x * κ) : GA D A × GA D WW) = (g, x) * (1, κ) := by simp
    rw [hm, map_mul, Module.End.mul_apply, ← e1, hpt, e1, hfix]
end GlobalTheory.BottomLevel
end
end
