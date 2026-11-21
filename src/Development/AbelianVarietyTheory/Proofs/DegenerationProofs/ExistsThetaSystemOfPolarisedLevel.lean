import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanTranslatesMultiplicationPullbackTheta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_fg_subalgebra_spec_factors_open (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (R : Subalgebra o Ω) (hR : R.FG) (V : (Sp R).Opens) (hV : (V : Set (Sp R)).Nonempty) :
    ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧
      ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  classical
  obtain ⟨x, hx⟩ := hV
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := x) (u := (V : Set (Sp R))) hx V.isOpen
  have hf0 : (f : Ω) ≠ 0 := by
    intro h0
    have : f = 0 := Subtype.ext h0
    subst this
    exact hxf (Ideal.zero_mem _)
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (({(f : Ω)⁻¹} : Finset Ω) : Set Ω)
  have h : R ≤ R' := le_sup_left
  have hinv : (f : Ω)⁻¹ ∈ R' :=
    (le_sup_right : _ ≤ R') (Algebra.subset_adjoin (by simp))
  refine ⟨R', h, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩
  have hu : IsUnit ((Subalgebra.inclusion h).toRingHom f) :=
    IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : R') (Subtype.ext (mul_inv_cancel₀ hf0))
  refine ⟨IsOpenImmersion.lift V.ι (spMap (Subalgebra.inclusion h).toRingHom) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  apply hfV
  intro hm
  exact y.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)

end GlobalTheory
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_spec_factor_through_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω), R.FG → ∀ V : (Sp R).Opens, (V : Set (Sp R)).Nonempty → ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧ ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  atlas_forward_decl GlobalTheory.exists_fg_subalgebra_spec_factors_open
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalBasis_move_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  first | exact @GlobalTheory.UnivBasisMove.univBasis_move | exact GlobalTheory.UnivBasisMove.univBasis_move | (intros; apply GlobalTheory.UnivBasisMove.univBasis_move <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory

theorem exists_level_baseChange : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  intro hL S S' _ _ f P P' φ h hiso hg k ze ze' hz hprim lev
  have e : 2 * P'.g = 2 * P.g := congrArg (2 * ·) hg
  have cast : ∀ {n n' : ℕ} (e : n' = n) {T : Over S} (y : Fin n → (T ⟶ P.A)) (a : Fin n' → ℕ),
      linComb (fun i => y (Fin.cast e i)) a = linComb y (fun i => a (Fin.cast e.symm i)) := by
    intro n n' e T y a
    subst e
    rfl
  choose pt hpt using fun i => ThetaObjPull.exists_sec h (lev.pt (Fin.cast e i))
  have hpt' : ∀ i, (pt i).left ≫ φ = f ≫ (lev.pt (Fin.cast e i)).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have key : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ S') (c : Fin (2 * P'.g) → ℕ),
      pushHom h (Over.mk x) (linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S') ≫ pt i) c) =
      linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ baseOver S) ≫ lev.pt i)
        (fun i => c (Fin.cast e.symm i)) := fun K _ x c => by
    rw [ThetaObjPull.map_linComb]
    refine Eq.trans ?_ (cast e _ c)
    congr 1
    funext i
    apply Over.OverMorphism.ext
    show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (lev.pt _).left
    rw [Category.assoc, hpt', Category.assoc]
  have := P.isAb.comm
  refine ⟨{ pt := pt
            prim := hprim
            torsion := fun i => ThetaObjPull.pushHom_injective h _ ?_
            indep := fun K _ _ x c c' hc => ?_
            span := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_ }, fun i i' hi => ?_⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (ThetaObjPull.toBase f)) _ _).symm.trans (by rw [lev.torsion, map_one])
  · have q := lev.indep K (x ≫ f) (fun i => c (Fin.cast e.symm i)) (fun i => c' (Fin.cast e.symm i))
      ((key K x _).symm.trans ((congrArg (pushHom h (Over.mk x)) hc).trans (key K x _)))
    funext i
    exact congrFun q (Fin.cast e i)
  · have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc⟩ := lev.span K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨fun i => c (Fin.cast e i), ThetaObjPull.pushHom_injective h _ ((key K x _).trans hc)⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ P.isLB P'.isLB h hiso (baseOver S') k (pt i) (pt j)
      (ThetaObjPull.toBase f ≫ lev.pt _) (ThetaObjPull.toBase f ≫ lev.pt _) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (ThetaObjPull.toBase f)
      (lev.pairing (Fin.cast e i) (Fin.cast e j))
    rw [map_zpow] at w
    have e₁ : Units.map (ThetaObjPull.toBase f).left.appTop.hom.toMonoidHom ze = ze' := Units.ext hz
    have e₂ : stdSymp P.g (Fin.cast e i) (Fin.cast e j) = stdSymp P'.g i j := by
      simp only [stdSymp, Fin.val_cast, hg]
    rw [e₁, e₂] at w
    exact w
  · obtain rfl : i = Fin.cast e i' := Fin.ext hi
    exact hpt' i'

end GlobalTheory
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_baseChange_polarisedAbelian : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  first | exact @GlobalTheory.exists_level_baseChange | exact GlobalTheory.exists_level_baseChange | (intros; apply GlobalTheory.exists_level_baseChange <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoints_of_squareLevel_alt : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  first | exact @GlobalTheory.exists_torsionPoints_of_squareLevel | exact GlobalTheory.exists_torsionPoints_of_squareLevel | (intros; apply GlobalTheory.exists_torsionPoints_of_squareLevel <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symLift_of_pow_eq_one : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k → IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  first | exact @GlobalTheory.exists_symLift_global | exact GlobalTheory.exists_symLift_global | (intros; apply GlobalTheory.exists_symLift_global <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTorsFrame_of_symLift' : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  first | exact @GlobalTheory.exists_isTorsFrame_of_symLift | exact GlobalTheory.exists_isTorsFrame_of_symLift | (intros; apply GlobalTheory.exists_isTorsFrame_of_symLift <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_mulPull_iso_origin : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  first | exact @GlobalTheory.ThetaReal.exists_normalised_mulPull | exact GlobalTheory.ThetaReal.exists_normalised_mulPull | (intros; apply GlobalTheory.ThetaReal.exists_normalised_mulPull <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_translates_multiplicationPullback_theta : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(S, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ (κ : Type) [Fintype κ] (b : κ → SecM P.A P.L N (baseOver S)), UnivBasis P N b → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver S)), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver S)) (t : I → LB.Sec (LPow P.A P.L N (baseOver S))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver S).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver S))) = ⊤ := by
  first | exact @GlobalTheory.ThetaReal.span_translates_mulPull | exact GlobalTheory.ThetaReal.span_translates_mulPull | (intros; apply GlobalTheory.ThetaReal.span_translates_mulPull <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaReal
open GlobalTheory.ThetaPtMove

theorem exists_good_translate : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  intro hL S P K _ _ x n hn hK th hth a
  let β : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := hth (Over.mk x) β
  have h₀ : SecM.ofSec P.A (VVRank.pullS P.A 1 β th) ≠ 0 := fun e => c.ne_zero 0 ((hc 0).trans e)
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange P x hn hK _ h₀ a
  refine ⟨y, hy, fun z τ v hz _ hv h0 => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.isLB p
  have q := hu p J hJ
  have e : (ptSecT P.A (a * y)).left ≫ (β ▷ P.A).left = β.left ≫ (ptSecT P.A z).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← hz]
    congr 1
    ext1 <;> simp [ptSecT, β]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e, sv_of_isValueAt hv _ p hJ, h0,
    GlobalTheory.UT.ExactTerm.gs_zero' β.left p ⊤ trivial, MulZeroClass.zero_mul] at q
  exact not_isUnit_zero q

end GlobalTheory.ThetaReal
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_torsion_translate_geometricPoint : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  first | exact @GlobalTheory.ThetaReal.exists_good_translate | exact GlobalTheory.ThetaReal.exists_good_translate | (intros; apply GlobalTheory.ThetaReal.exists_good_translate <;> assumption)
end

section
namespace GlobalTheory.ThetaReal

theorem zmod_pow_exists_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : 1 ≤ n) (hJ : 2 ≤ J)
    (y : ZMod (n ^ J)) (hy : n • y = 0) : ∃ w : ZMod (n ^ J), y = n • w := by
  haveI : NeZero (n ^ J) := ⟨pow_ne_zero _ (by omega)⟩
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hy
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 2 := ⟨J - 2, by omega⟩
  have h1 : n * (n * n ^ j) ∣ n * k := by
    have : n * (n * n ^ j) = n ^ (j + 2) := by ring
    rw [this]; exact hy
  have h2 : n * n ^ j ∣ k := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
  obtain ⟨c, rfl⟩ := (Dvd.intro _ rfl : n ∣ n * n ^ j).trans h2
  exact ⟨(c : ZMod (n ^ (j + 2))), by rw [nsmul_eq_mul, Nat.cast_mul]⟩

theorem closure_eq_top_of_meets_torsion_cosets :
    ∀ (κ : Type) (n J M : ℕ), 1 ≤ n → 2 ≤ J → M = n ^ J → ∀ X : Set (κ → ZMod M),
      (∀ a : κ → ZMod M, ∃ y : κ → ZMod M, n • y = 0 ∧ a + y ∈ X) →
      AddSubgroup.closure X = ⊤ := by
  intro κ n J M hn hJ hM X hX
  subst hM
  have step : ∀ a : κ → ZMod (n ^ J), ∃ w : κ → ZMod (n ^ J),
      a + n • w ∈ AddSubgroup.closure X := by
    intro a
    obtain ⟨y, hy, hay⟩ := hX a
    have : ∀ i, ∃ w : ZMod (n ^ J), y i = n • w := fun i =>
      zmod_pow_exists_nsmul_of_nsmul_eq_zero n J hn hJ (y i) (congrFun hy i)
    choose w hw using this
    refine ⟨w, ?_⟩
    have : n • w = y := funext fun i => (hw i).symm
    rw [this]
    exact AddSubgroup.subset_closure hay
  have ind : ∀ (i : ℕ) (a : κ → ZMod (n ^ J)), ∃ w : κ → ZMod (n ^ J),
      a + n ^ i • w ∈ AddSubgroup.closure X := by
    intro i
    induction i with
    | zero => intro a; exact ⟨-a, by simp⟩
    | succ i ih =>
      intro a
      obtain ⟨w, hw⟩ := ih a
      obtain ⟨v, hv⟩ := step (-w)
      refine ⟨v, ?_⟩
      have h := (AddSubgroup.closure X).add_mem hw ((AddSubgroup.closure X).nsmul_mem hv (n ^ i))
      have e : a + n ^ i • w + n ^ i • (-w + n • v) = a + n ^ (i + 1) • v := by
        rw [smul_add, smul_neg, smul_smul, pow_succ]; abel
      rwa [e] at h
  rw [eq_top_iff]
  intro a _
  obtain ⟨w, hw⟩ := ind J a
  have : n ^ J • w = 0 := by
    funext i
    show n ^ J • w i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rwa [this, add_zero] at hw

end GlobalTheory.ThetaReal
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_zmodPow_eq_top_of_meets_torsion_cosets : ∀ (κ : Type) (n J M : ℕ), 1 ≤ n → 2 ≤ J → M = n ^ J → ∀ X : Set (κ → ZMod M), (∀ a : κ → ZMod M, ∃ y : κ → ZMod M, n • y = 0 ∧ a + y ∈ X) → AddSubgroup.closure X = ⊤ := by
  first | exact @GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets | exact GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets | (intros; apply GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monomial_matrices_projectiveRep : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  first | exact @GlobalTheory.ThetaReal.exists_monomial_matrices | exact GlobalTheory.ThetaReal.exists_monomial_matrices | (intros; apply GlobalTheory.ThetaReal.exists_monomial_matrices <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaReal

theorem exists_nsmul_eq {κ : Type} {r N : ℕ} (h : 1 ≤ r * N) (a : κ → ZMod (r * N)) (ha : N • a = 0) :
    ∃ c : κ → ZMod (r * N), a = r • c := by
  haveI : NeZero (r * N) := ⟨by omega⟩
  have hN : 0 < N := Nat.pos_of_mul_pos_left h
  have key : ∀ i, r ∣ (a i).val := fun i => by
    have e : ((N * (a i).val : ℕ) : ZMod (r * N)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
      exact congrFun ha i
    rw [ZMod.natCast_eq_zero_iff, mul_comm N] at e
    exact Nat.dvd_of_mul_dvd_mul_right hN e
  choose c hc using key
  refine ⟨fun i => (c i : ZMod (r * N)), funext fun i => ?_⟩
  rw [Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, ← hc, ZMod.natCast_zmod_val]

theorem fn_hom {R : Type} [CommRing R] (v : Γ((baseOver (Sp R)).left, ⊤)) :
    fn ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom v) = v :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply v

theorem fn_injective {R : Type} [CommRing R] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isNoetherian_of_fg [ArithBase o Ω] {R : Subalgebra o Ω} (h : R.FG) : IsNoetherianRing R := by
  have := ArithBase.ded (o := o) (Ω := Ω)
  exact isNoetherianRing_of_fg h

theorem algebraMap_injective [ArithBase o Ω] (R : Subalgebra o Ω) : Function.Injective (algebraMap o R) :=
  fun _ _ h => ArithBase.inj (o := o) (Ω := Ω) (congrArg Subtype.val h)

theorem prim_iff [ArithBase o Ω] (R : Subalgebra o Ω) (ze : oˣ) (q : ℕ) :
    IsPrimitiveRoot (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) q ↔ IsPrimitiveRoot (ze : o) q := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact IsPrimitiveRoot.map_iff_of_injective
    (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R))
    (fn_injective.comp (algebraMap_injective R))

theorem exists_real_of_univBasis (hL : Laws) [ArithBase o Ω] (R : Subalgebra o Ω) (fg : R.FG)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ) (hp : n.Prime)
    (ho : Odd n) (hk : 2 ≤ k) (hj : 1 ≤ j) (hu : IsUnit (n : o)) (hS : HypS P.A P.L)
    (lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)))
    (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))) (hth : UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th))
    (b : Fin (((n ^ k) ^ 2) ^ P.g) → SecM P.A P.L ((n ^ k) ^ 2 : ℕ) (baseOver (Sp R)))
    (hb : UnivBasis P ((n ^ k) ^ 2 : ℕ) b) {R₀ : Subalgebra o Ω} (h : R₀ ≤ R) (P₀ : PolAV (Sp R₀))
    (φ : P.A.left ⟶ P₀.A.left) (hg : P.g = P₀.g)
    (hφ : IsGrpPullback P.A P₀.A (spMap (Subalgebra.inclusion h).toRingHom) φ) (hiso : LBIso P.L (P₀.L.pull φ))
    (x₀ : Fin (2 * P₀.g) → (baseOver (Sp R₀) ⟶ P₀.A))
    (hx₀ : ∀ (i : Fin (2 * P₀.g)) (i' : Fin (2 * P.g)), (i : ℕ) = i' →
      (lev.pt i').left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i).left) :
    ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R₀ ≤ S.R) (φ : ρ.P.A.left ⟶ P₀.A.left), S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧
      S.r = n ^ j ∧ S.g = P₀.g ∧ IsGrpPullback ρ.P.A P₀.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧
      LBIso ρ.P.L (P₀.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P₀.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P₀.g →
      (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ =
        spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i₁ ^ (S.r * S.N)).left ∧
      (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ =
        spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i₂ ^ (S.r * S.N)).left := by
  haveI := isNoetherian_of_fg fg
  haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  have hn2 : 2 ≤ n := hp.two_le
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn1
  have hr1 : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn1
  have hN2 : 2 ≤ (n ^ k) ^ 2 := by
    have : n ^ 1 ≤ n ^ k := Nat.pow_le_pow_right hn1 (by omega)
    nlinarith
  have hM : n ^ j * (n ^ k) ^ 2 = n ^ (j + 2 * k) := by ring
  have hM1 : 1 ≤ n ^ j * (n ^ k) ^ 2 := hM ▸ Nat.one_le_pow _ _ hn1
  have hMo : Odd (n ^ j * (n ^ k) ^ 2) := hM ▸ ho.pow
  let f : o →+* Γ((baseOver (Sp R)).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R)
  have hf : Function.Injective f := fn_injective.comp (algebraMap_injective R)
  haveI : Nontrivial Γ((baseOver (Sp R)).left, ⊤) := (fn_injective (R := R)).nontrivial
  have un : ∀ q e : ℕ, q = n ^ e → IsUnit (q : Γ(Sp R, ⊤)) := fun q e hq => by
    have := (hu.pow e).map f
    rw [map_pow, map_natCast] at this
    rw [hq, Nat.cast_pow]
    exact this
  have prim : IsPrimitiveRoot (ze : o) ((n ^ j * (n ^ k) ^ 2) ^ 2) := (prim_iff R ze _).1 lev.prim
  obtain ⟨pt, hadd, hbij, hweil, hdiv, hnorm⟩ := GlobalTheory.T.exists_torsionPoints_of_squareLevel_alt hL _ P _ _ hM1 (un _ _ hM) lev
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  obtain ⟨rig, hrig⟩ := P.rigid
  have hfr : ∀ a, ∃ τ, IsTorsFrame P rig (n ^ j * (n ^ k) ^ 2) (pt a) τ := fun a => by
    obtain ⟨y, hy, e⟩ := hdiv a
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P _ hMo.pow (un _ ((j + 2 * k) * 2) (by rw [hM, pow_mul])) _ y hy
    exact GlobalTheory.T.exists_isTorsFrame_of_symLift' hL _ P rig hrig _ hMo _ y _ hy e θ hθ
  choose fr hfr using hfr
  have tors : ∀ a, pt (n ^ j • a) ^ ((n ^ k) ^ 2) = 1 := fun a => by
    rw [← hsm, smul_smul, mul_comm ((n ^ k) ^ 2) (n ^ j), nsmul_self, h0]
  choose U hU using fun a => GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P _ ho.pow.pow (un _ (k * 2) (pow_mul _ _ _).symm) _ _ (tors a)
  obtain ⟨α, hα, hαn⟩ := GlobalTheory.T.exists_normalised_mulPull_iso_origin hL _ P rig hrig (n ^ k) _ rfl (baseOver (Sp R))
  obtain ⟨s₀, hs₀⟩ := VVRank.exists_isTwistPull P.A (ψ := mulT P.A (baseOver (Sp R)) (n ^ k)) (hm := lift_snd _ _)
    (b := 1) P.isLB hα th
  obtain ⟨u, u₁, u₂, u₃, u₄, u₅⟩ := exists_operators hL P rfl ho.pow (un _ _ hM) _ pt hadd hweil U hU hα hs₀
  have hspan := GlobalTheory.T.span_translates_multiplicationPullback_theta hL _ P (n ^ k) _ rfl hm1 (un _ _ rfl) th hth _ b hb α hα s₀ hs₀ _ U
    (fun a => SecM.toSec P.A (u a (SecM.ofSec P.A s₀))) (fun K _ _ x z hz => by
      obtain ⟨a, ha, uniq⟩ := hbij K x z (by rw [mul_comm, pow_mul, hz, one_pow])
      obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
      have e : (n ^ k) ^ 2 • a = 0 := (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, ha, hz])).trans
        (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm
      obtain ⟨c, rfl⟩ := exists_nsmul_eq hM1 a e
      exact ⟨c, by rw [(hU c).pt_eq, ha]⟩) (fun a => (u₁ _ _ _).2 rfl)
  obtain ⟨bb, -⟩ := hb.exists_basis
  obtain ⟨J, _, ρ, s, i₀, hcard, hi₀, ρ₁, ρ₂, ρ₃, ρ₄, ρ₅⟩ := GlobalTheory.T.exists_monomial_matrices_projectiveRep o _ _ f hf P.g (n ^ k) (n ^ j) _ rfl hm1 hr1
    ze _ (Nat.one_le_pow _ _ hM1) prim.pow_eq_one bb u (SecM.ofSec P.A s₀) u₂
    (fun a b => (u₃ a b).imp fun e he v => (he v).trans (congrArg (· • _) (map_pow f _ _).symm)) u₄ u₅ hspan
  choose v hv using fun a => ThetaPtExist.exists_isValueAt P.isLB th (pt a) (fr a) (hfr a).2.1
  choose w hw using fun a i => (hL.evVal _ P ((n ^ k) ^ 2) (pt a) (fr a) (hfr a).2.1 (SecM.toSec P.A (s i))).exists
  let ev : Γ((baseOver (Sp R)).left, ⊤) → R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have good : ∀ a, ∃ y, n • y = 0 ∧ a + y ∈ {a | (ev (v a) : Ω) ≠ 0} := fun a => by
    let K := AlgebraicClosure Ω
    let x : Sp K ⟶ Sp R := spMap ((algebraMap Ω K).comp R.val.toRingHom)
    have := ArithBase.char (o := o) (Ω := Ω)
    obtain ⟨y, hy, H⟩ := GlobalTheory.T.exists_good_torsion_translate_geometricPoint hL _ P K x n hn2 (Nat.cast_ne_zero.2 (by omega)) th hth
      ((Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a)
    obtain ⟨c, hc, -⟩ := hbij K x y (by rw [hM, show j + 2 * k = (j + 2 * k - 1) + 1 by omega, pow_succ', pow_mul, hy,
      one_pow])
    obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
    refine ⟨c, (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
      (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun e => ?_⟩
    refine H (pt (a + c)) (fr _) (v _) (by rw [hadd, MonObj.comp_mul, hc]) (hfr _).2.1 (hv _) ?_
    have e' : ev (v (a + c)) = 0 := Subtype.ext e
    exact (fn_hom _).symm.trans ((congrArg fn e').trans (map_zero _))
  obtain ⟨c₁, hc₁⟩ := hth.exists_basis
  let S : ThetaSys o Ω :=
    { g := P.g, N := (n ^ k) ^ 2, r := n ^ j, N_ge := hN2, r_pos := hr1, ζ := ze, prim := prim
      unit := by rw [hM, Nat.cast_pow]; exact hu.pow _
      J := J, ne := ⟨i₀⟩, ρ := ρ, ρ_one := ρ₁, ρ_mul := ρ₂, ρ_add := ρ₃
      th := fun a => ev (v a), ev := fun a i => ev (w a i), R := R, fg := fg, frac := frac
      th_mem := fun a => (ev (v a)).2, ev_mem := fun a i => (ev (w a i)).2
      supp := GlobalTheory.T.closure_zmodPow_eq_top_of_meets_torsion_cosets _ n (j + 2 * k) _ hn1 (by omega) hM _ good
      th_ne := by
        obtain ⟨y, -, hy⟩ := good 0
        exact ⟨_, hy⟩ }
  let ρ' : S.Real :=
    { P := P, g_eq := rfl, hypS := hS, n := n, n_prime := hp, n_odd := ho, k := k, two_le := hk, N_eq := rfl
      r_eq := ⟨j, hj, rfl⟩, card := hcard, pt := pt, pt_add := hadd, pt_bij := hbij
      weil := fun a b c hc => by
        have e : unitOn c = unitOn (Units.map (algebraMap o R).toMonoidHom ze) ^
            (n ^ j * (n ^ k) ^ 2 * (eStd P.g _ a b).val) := Units.ext
          ((congrArg fn hc).trans ((map_pow f _ _).trans (Units.val_pow_eq_pow_val (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) _).symm))
        rw [e]
        exact hweil a b
      rig := rig, rig_gen := hrig, th₁ := th
      th₁_basis := fun σ => by
        have := existsUnique_of_basis c₁ σ
        simp only [hc₁] at this
        exact this
      fr := fr, fr_tors := hfr
      th_val := fun a => (fn_hom (v a)).symm ▸ hv a
      s := fun i => SecM.toSec P.A (s i)
      s_basis := existsUnique_of_basis s
      ev_val := fun i a => (congrArg (IsValueAt _ _ _ _ _ _) (fn_hom (w a i))).mpr (hw a i)
      i₀ := i₀, α := α, α_gen := hα, α_norm := hαn
      s_zero := by
        have e : SecM.toSec P.A (s i₀) = s₀ := by rw [hi₀]; rfl
        exact e ▸ hs₀
      U := U, U_sym := hU
      U_act := fun a i σ H => (sum_iff σ s _).2 (((u₁ _ _ _).1 H).symm.trans (ρ₄ a i))
      orbit := ρ₅ }
  refine ⟨S, ρ', h, φ, rfl, rfl, rfl, hg, hφ, hiso, fun i i₁ i₂ e₁ e₂ => ?_⟩
  obtain ⟨q₁, q₂⟩ := hnorm i ⟨i₁, by have := i₁.2; omega⟩ ⟨i₂, by have := i₂.2; omega⟩ e₁
    (e₂.trans (congrArg (_ + ·) hg.symm))
  have key : ∀ (i : Fin (2 * P₀.g)) (i' : Fin (2 * P.g)) (q : ℕ), (i : ℕ) = i' →
      (lev.pt i' ^ q).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i ^ q).left := fun i i' q e =>
    (ThetaPtMove.over_pow hφ (T := baseOver (Sp R)) (T₀ := baseOver (Sp R₀)) _
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hx₀ i i' e).symm q).symm
  exact ⟨(congrArg (fun z => z.left ≫ φ) q₁).trans (key _ _ _ rfl),
    (congrArg (fun z => z.left ≫ φ) q₂).trans (key _ _ _ rfl)⟩

end GlobalTheory.ThetaReal

open GlobalTheory.ThetaReal in

theorem GlobalTheory.ThetaReal.exists_thetaSys_real : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₁ ^ (S.r * S.N)).left ∧ (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₂ ^ (S.r * S.N)).left := by
  intro hL hL₂ o Ω _ _ _ _ R fg frac P n k j ze hp ho hk hj hu hS lev
  haveI := isNoetherian_of_fg fg
  let p : Sp R := (⊥ : PrimeSpectrum R)
  obtain ⟨V₁, m₁, b₁, hb₁⟩ := exists_univBasis hL₂.secBaseChangeAny P 1 le_rfl p
  obtain ⟨V₂, m₂, b₂, hb₂⟩ := exists_univBasis hL₂.secBaseChangeAny P ((n ^ k) ^ 2)
    (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hp.pos)) p
  obtain ⟨R', h, fg', τ, hτ⟩ := GlobalTheory.T.exists_fg_subalgebra_spec_factor_through_open o Ω R fg (V₁ ⊓ V₂) ⟨p, m₁, m₂⟩
  haveI := isNoetherian_of_fg fg'
  obtain ⟨P', φ, hg, hφ, hiso⟩ := exists_isPolFibre hL.polBaseChange (Subalgebra.inclusion h).toRingHom P
  have hiso' := LBIso.symm hiso
  have w : ∀ (V : (Sp R).Opens) (hV : V₁ ⊓ V₂ ≤ V), (τ ≫ (Sp R).homOfLE hV) ≫ (overRes (T := baseOver (Sp R)) V).hom =
      spMap (Subalgebra.inclusion h).toRingHom := fun V hV => by
    change (τ ≫ (Sp R).homOfLE hV) ≫ V.ι ≫ 𝟙 _ = _
    rw [Category.comp_id, Category.assoc, Scheme.homOfLE_ι, hτ]
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso' _ _ _ _ (w V₁ inf_le_left) b₁ hb₁
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso' _ _ _ _ (w V₂ inf_le_right) b₂ hb₂
  obtain ⟨lev', hlev⟩ := GlobalTheory.T.exists_symplecticLevel_baseChange_polarisedAbelian hL _ _ _ P P' φ hφ hiso' hg _ _
    (unitOn (Units.map (algebraMap o R').toMonoidHom ze))
    (congrArg (fun q => q.hom (algebraMap o R ze))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom))).symm
    ((prim_iff R' ze _).2 ((prim_iff R ze _).1 lev.prim)) lev
  haveI hU : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let e := finCongr (congrArg (((n ^ k) ^ 2) ^ ·) hg)
  refine exists_real_of_univBasis hL R' fg' (fun x => ?_) P' n k j ze hp ho hk hj hu
    (SymBaseChange.hypS_baseChange _ _ _ _ _ φ _ _ P.isLB P'.isLB hφ hiso' hS) lev' (SecM.toSec P'.A (c₁ hU.default))
    hc₁.unique (fun i => c₂ (e i)) (fun T _ u => ?_) h P φ hg hφ hiso' lev.pt hlev
  · obtain ⟨a, ha, b, hb, e⟩ := frac x
    exact ⟨a, h ha, b, h hb, e⟩
  · obtain ⟨c, hc⟩ := hc₂ T u
    exact ⟨c.reindex e.symm, fun i => by rw [Module.Basis.reindex_apply, hc, Equiv.symm_symm]⟩

end
end
