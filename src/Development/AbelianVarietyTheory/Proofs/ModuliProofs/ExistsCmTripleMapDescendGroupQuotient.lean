module

import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsMultiplicativeGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfQuotientOfRigid
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientExistsUniqueCompEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace SabMapDescent

section Bundles

variable {X Y : Scheme.{0}}

def chartPullDivPull (A B : LB X) (h : Y ⟶ X) :
    ChartPull ((LB.div B A).pull h) (LB.div (B.pull h) (A.pull h)) (𝟙 Y) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have b := mem_pull.1 hj'
    refine (gm_pull_g _ h (𝟙 Y) y J J' hj hj').trans ((gm_div A B (𝟙 Y ≫ h) y _ _ ⟨a, b⟩).trans (Eq.symm ?_))
    refine (gm_div (A.pull h) (B.pull h) (𝟙 Y) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, ⟨mem_pull.2 b.1, mem_pull.2 b.2⟩⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹) (gm_pull_g B h (𝟙 Y) y _ _ (mem_pull.2 a.1) (mem_pull.2 b.1))
      (gm_pull_g A h (𝟙 Y) y _ _ (mem_pull.2 a.2) (mem_pull.2 b.2))

theorem lbIso_of_gen_of_gen {A B : LB X} (s : A.Gen) (hs : s.IsGen) (t : B.Gen) (ht : t.IsGen) : LBIso A B := by
  apply GlobalTheory.ZH.AbelianFibre.lbIso_of_gens <;> assumption

end Bundles

def IsQuot {Γ : Type} [Group Γ] {X X' : Scheme.{0}} (ρ : Γ →* Aut X) (π : X ⟶ X') : Prop :=
  IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧
    ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) →
      f ∈ Set.range (π.app V).hom

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem IsQuot.epi {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π) : Epi π :=
  ⟨fun {T} a b e => (quotient_existsUnique_comp_eq Γ X X' ρ π h T (π ≫ a)
    fun g => by rw [← Category.assoc, h.2.1 g]).unique rfl e.symm⟩

theorem IsQuot.epi_of_isPullback {X X' Y Y' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π)
    {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'} (H : IsPullback φ p p' π) (hp : Flat p') : Epi φ := by
  have hbase := quotient_flat_baseChange Γ X X' Y Y' ρ π φ p p' h H hp
  obtain ⟨hex, hall⟩ := hbase
  obtain ⟨τ, hτ⟩ := hex
  exact IsQuot.epi (hall τ hτ)

omit [Finite Γ] in
theorem IsQuot.isReduced {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π) [IsReduced X] :
    IsReduced X' :=
  ⟨fun V => isReduced_of_injective (π.app V).hom (h.2.2 V).1⟩

theorem exists_isPullback {U U' X' P P' P₁ : Scheme.{0}} {ρ : Γ →* Aut U} {r : U ⟶ U'} (hq : IsQuot ρ r)
    {j : U' ⟶ X'} {p : P ⟶ U} {p' : P' ⟶ U'} {p₁ : P₁ ⟶ X'} [Flat p'] [Flat p₁] {φ : P ⟶ P'} {n : P ⟶ P₁}
    (hφ : IsPullback φ p p' r) (hn : IsPullback n p p₁ (r ≫ j)) (τ : Γ →* Aut P)
    (hτ : ∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ n = n) :
    ∃ ψ : P' ⟶ P₁, φ ≫ ψ = n ∧ IsPullback ψ p' p₁ j := by
  have hφq : IsQuot τ φ := (quotient_flat_baseChange Γ U U' P P' ρ r φ p p' hq hφ inferInstance).2 τ
    fun g => ⟨(hτ g).2.1, (hτ g).1⟩
  have := hφq.epi
  obtain ⟨ψ, hψ, -⟩ := quotient_existsUnique_comp_eq Γ _ _ τ φ hφq _ n fun g => (hτ g).2.2
  have w : ψ ≫ p₁ = p' ≫ j := by
    rw [← cancel_epi φ, ← Category.assoc, hψ, hn.w, ← Category.assoc, ← hφ.w, Category.assoc]
  have H := IsPullback.of_hasPullback p₁ j
  let θ : P' ⟶ pullback p₁ j := pullback.lift ψ p' w
  have h₁ : θ ≫ pullback.fst p₁ j = ψ := pullback.lift_fst _ _ _
  have h₂ : θ ≫ pullback.snd p₁ j = p' := pullback.lift_snd _ _ _
  have hκ : IsPullback (φ ≫ θ) p (pullback.snd p₁ j) r :=
    IsPullback.of_right (by rw [Category.assoc, h₁, hψ]; exact hn) (by rw [Category.assoc, h₂, hφ.w]) H
  have hκq : IsQuot τ (φ ≫ θ) := (quotient_flat_baseChange Γ U U' P _ ρ r _ p _ hq hκ inferInstance).2 τ
    fun g => ⟨by rw [← Category.assoc, (hτ g).2.1], (hτ g).1⟩
  have := hκq.epi
  obtain ⟨σ, hσ, -⟩ := quotient_existsUnique_comp_eq Γ _ _ τ _ hκq _ φ fun g => (hτ g).2.1
  have : IsIso θ := ⟨σ, by rw [← cancel_epi φ, ← Category.assoc, hσ, Category.comp_id],
    by rw [← cancel_epi (φ ≫ θ), ← Category.assoc, hσ, Category.comp_id]⟩
  refine ⟨ψ, hψ, ?_⟩
  have := (IsPullback.of_horiz_isIso (fst := θ) (snd := p') (f := pullback.snd p₁ j) (g := 𝟙 U')
    ⟨by rw [h₂, Category.comp_id]⟩).paste_horiz H
  rwa [h₁, Category.id_comp] at this

theorem isGrpPullback_of_quot {U U' X' : Scheme.{0}} {ρ : Γ →* Aut U} {r : U ⟶ U'} (hq : IsQuot ρ r)
    {j : U' ⟶ X'} {G : Over U} {G' : Over U'} {G₁ : Over X'} [GrpObj G] [GrpObj G'] [GrpObj G₁] [Flat G'.hom]
    {φ : G.left ⟶ G'.left} {ψ : G'.left ⟶ G₁.left} (hφ : IsGrpPullback G G' r φ)
    (hn : IsGrpPullback G G₁ (r ≫ j) (φ ≫ ψ)) (hψ : IsPullback ψ G'.hom G₁.hom j) :
    IsGrpPullback G' G₁ j ψ := by
  have key : ∀ (T : Over U') (x y : T ⟶ G'), Flat T.hom →
      (pushPt hψ.w x * pushPt hψ.w y).left = (x * y).left ≫ ψ := by
    intro T x y hT
    have H := IsPullback.of_hasPullback T.hom r
    have := hq.epi_of_isPullback H hT
    let q := pullback.fst T.hom r
    let W : Over U := Over.mk (pullback.snd T.hom r)
    let l : (T ⟶ G') → (W ⟶ G) := fun z => Over.homMk
      (hφ.1.lift (q ≫ z.left) (pullback.snd T.hom r) (by rw [Category.assoc, Over.w z]; exact H.w))
      (hφ.1.lift_snd _ _ _)
    have hl : ∀ z, (l z).left ≫ φ = q ≫ z.left := fun z => hφ.1.lift_fst _ _ _
    let q' : Over.mk (W.hom ≫ r) ⟶ T := Over.homMk q H.w
    let q₁ : Over.mk (W.hom ≫ r ≫ j) ⟶ Over.mk (T.hom ≫ j) := Over.homMk q (by
      show q ≫ T.hom ≫ j = pullback.snd T.hom r ≫ r ≫ j
      rw [← Category.assoc, H.w, Category.assoc])
    have e₁ := hφ.2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
    have e₂ := hn.2 W (l x) (l y) (q₁ ≫ pushPt hψ.w x) (q₁ ≫ pushPt hψ.w y)
      (by rw [← Category.assoc (l x).left, hl, Category.assoc]; rfl)
      (by rw [← Category.assoc (l y).left, hl, Category.assoc]; rfl)
    rw [← MonObj.comp_mul] at e₁ e₂
    rw [← Category.assoc (l x * l y).left, ← e₁] at e₂
    rw [← cancel_epi q, ← Category.assoc q]
    exact e₂
  refine ⟨hψ, fun T x y x₀ y₀ hx hy => ?_⟩
  have hf : Flat (G' ⊗ G').hom := inferInstanceAs (Flat (pullback.fst G'.hom G'.hom ≫ G'.hom))
  have e := key (G' ⊗ G') (fst _ _) (snd _ _) hf
  let z : Over.mk (T.hom ≫ j) ⟶ Over.mk ((G' ⊗ G').hom ≫ j) := Over.homMk (lift x y).left (by
    show (lift x y).left ≫ (G' ⊗ G').hom ≫ j = T.hom ≫ j
    rw [← Category.assoc, Over.w])
  have hx' : x₀ = z ≫ pushPt hψ.w (fst _ _) := Over.OverMorphism.ext (by
    show _ = (lift x y).left ≫ (fst G' G').left ≫ ψ
    rw [← Category.assoc, ← Over.comp_left, lift_fst, hx])
  have hy' : y₀ = z ≫ pushPt hψ.w (snd _ _) := Over.OverMorphism.ext (by
    show _ = (lift x y).left ≫ (snd G' G').left ≫ ψ
    rw [← Category.assoc, ← Over.comp_left, lift_snd, hy])
  have hxy : x * y = lift x y ≫ (fst G' G' * snd G' G') := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hx', hy', ← MonObj.comp_mul, hxy, Over.comp_left, e, Over.comp_left, Category.assoc]
  rfl

theorem subset_abLocus {S : Scheme.{0}} (G : Over S) [IsProper G.hom] (A : Set S) : A ⊆ abLocus G :=
  fun _ _ _ _ _ _ _ => inferInstance

end SabMapDescent


open SabMapDescent in
theorem exists_sabMap_of_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (U U' X' : Scheme.{0}) (ρ : Γ →* Aut U) (r : U ⟶ U') (t : SAB H U) (t' : SAB H U') (t₁ : SAB H X') (τ : Γ →* Aut t.G.left) (ν : SABMap t t' r) (j : U' ⟶ X') (n : SABMap t t₁ (r ≫ j)), (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsReduced U → IsProper t.G.hom → (∀ g, (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ ν.φ = ν.φ ∧ (τ g).asIso.hom ≫ n.φ = n.φ) → ∃ n' : SABMap t' t₁ j, ν.φ ≫ n'.φ = n.φ := by
  intro E _ _ _ H Γ _ _ U U' X' ρ r t t' t₁ τ ν j n hq hred hprop hτ
  have hq : IsQuot ρ r := hq
  have := t.semi.smooth
  have := t.semi.geomConnected
  have := t'.semi.smooth
  have := t'.semi.separated
  have := t₁.semi.smooth
  obtain ⟨ψ, hψ, hpb⟩ := exists_isPullback hq ν.cart.1 n.cart.1 τ hτ
  have hgp : IsGrpPullback t'.G t₁.G j ψ := isGrpPullback_of_quot hq ν.cart (hψ ▸ n.cart) hpb
  have := hq.epi_of_isPullback ν.cart.1 inferInstance
  obtain ⟨hint, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ U U' ρ r hq
  have : Surjective ν.cm.F := MorphismProperty.of_isPullback (P := @Surjective) ν.cart.1.flip hsurj
  have : UniversallyClosed (ν.cm.F ≫ t'.G.hom) := by rw [ν.cart.1.w]; infer_instance
  have : UniversallyClosed t'.G.hom := .of_comp_surjective ν.cm.F _
  have : IsProper t'.G.hom := {}
  have he : eSec t.G ≫ t.G.hom = 𝟙 U := Over.w η[t.G]
  have he' : eSec t'.G ≫ t'.G.hom = 𝟙 U' := Over.w η[t'.G]
  have hiso : LBIso t'.PP.L (t₁.PP.L.pull ψ) := by
    refine exists_gen_of_quotient_of_rigid Γ U U' ρ r t.G t'.G ν.cm.F (eSec t.G) (eSec t'.G)
      (LB.div (t₁.PP.L.pull ψ) t'.PP.L) hq ν.cart.1 inferInstance he he' (by rw [ν.cm.e_comm, ν.base])
      (eq_one_of_appLE_section_eq_one U t.G _ he inferInstance
        (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) ⟨hred, subset_abLocus _ _⟩)
      (LB.isLB_div (pull_isLB t₁.PP.isLB ψ) t'.PP.isLB) ?_ ?_
    · obtain ⟨c, hc⟩ := gen_chartPull (chartPullLinComb t₁.PP.L ψ (K := PUnit) (fun _ => eSec t'.G)
        (fun _ => eSec t₁.G) (fun _ => 1) j fun _ => (cubeMapOf hgp).e_comm) t₁.PP.rig t₁.PP.rigGen
      obtain ⟨w, hw⟩ := lbIso_of_gen_of_gen t'.PP.rig t'.PP.rigGen c hc
      exact gen_chartPull (chartPullDivPull _ _ _) w hw
    · obtain ⟨a, ha, -⟩ := ν.lin
      obtain ⟨b, hb, -⟩ := n.lin
      have hb' : LBIso t.PP.L ((t₁.PP.L.pull ψ).pull ν.cm.F) :=
        LBIso.chartPull (chartPullId _) (chartPullLinComb t₁.PP.L ψ (K := PUnit) (fun _ => ν.cm.F)
          (fun _ => n.cm.F) (fun _ => 1) (𝟙 _) fun _ => hψ.trans (Category.id_comp _).symm) ⟨b, hb⟩
      obtain ⟨w, hw⟩ := LBIso.trans (pull_isLB t'.PP.isLB _) t.PP.isLB
        (pull_isLB (pull_isLB t₁.PP.isLB ψ) _) (LBIso.symm ⟨a, ha⟩) hb'
      exact gen_chartPull (chartPullDivPull _ _ _) w hw
  obtain ⟨n', hn'⟩ := GlobalTheory.exists_sabMap_of_lbIso E H X' U' t₁ t' j ψ ⟨hq.isReduced, subset_abLocus _ _⟩ hgp (fun a => by
    rw [← cancel_epi ν.cm.F, ← Category.assoc, ← ν.act, Category.assoc, hψ, n.act, ← Category.assoc, hψ]) hiso
  exact ⟨n', hn' ▸ hψ⟩

end GlobalTheory
