module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CxPts

namespace GlobalTheory.ConstFn

variable {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ}

theorem ev_top_eq (a : Γ(X, ⊤)) (y : CxPts p σ) :
    ev p σ ⊤ a y = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (y.1.appTop.hom a) := by
  have h : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : X.Opens) := le_rfl
  show valR y.1 ⊤ a = _
  rw [valR, dite_eq_left h]
  rfl

theorem exists_ev_eq [UniversallyClosed p] [GeometricallyIntegral p] (a : Γ(X, ⊤)) :
    ∃ b : ℂ, ∀ y : CxPts p σ, ev p σ ⊤ a y = b := by
  have hZ : IsIntegral (pullback p (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := p) (spMap σ) _ _ (.of_hasPullback _ _)
  let fs := pullback.fst p (spMap σ)
  let sn := pullback.snd p (spMap σ)
  let e : ℂ →+* Γ(pullback p (spMap σ), ⊤) :=
    sn.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  letI : Algebra ℂ Γ(pullback p (spMap σ), ⊤) := e.toAlgebra
  have hcomp : (algebraMap ℂ Γ(pullback p (spMap σ), ⊤)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom) =
      fs.appTop.hom.comp p.appTop.hom := by
    have h : fs ≫ p = sn ≫ spMap σ := pullback.condition
    ext c
    have h' := congrArg (fun m : pullback p (spMap σ) ⟶ Sp F => m.appTop.hom c) h
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h'
    simp only [RingHom.comp_apply]
    refine Eq.trans ?_ h'.symm
    show sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
    simp
  have hint : IsIntegral ℂ (fs.appTop.hom a) := by
    obtain ⟨P, hP, h0⟩ := isIntegral_appTop_of_universallyClosed p a
    refine ⟨P.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
    (K := integralClosure ℂ Γ(pullback p (spMap σ), ⊤))).2 ⟨_, hint⟩
  have hr' : e r = fs.appTop.hom a := congrArg Subtype.val hr
  refine ⟨r, fun y => ?_⟩
  let z : Sp ℂ ⟶ pullback p (spMap σ) :=
    pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp])
  have h1 : z ≫ fs = y.1 := pullback.lift_fst _ _ _
  have h2 : z ≫ sn = 𝟙 _ := pullback.lift_snd _ _ _
  have h3 : y.1.appTop.hom a = z.appTop.hom (fs.appTop.hom a) := by
    rw [← h1, Scheme.Hom.comp_appTop]; rfl
  have h4 : z.appTop.hom (sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r := by
    have e₂ : (z ≫ sn).appTop = sn.appTop ≫ z.appTop := Scheme.Hom.comp_appTop _ _
    rw [h2] at e₂
    have e₃ := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) e₂
    exact Eq.trans e₃.symm (by simp)
  rw [ev_top_eq, h3, ← hr']
  show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (z.appTop.hom (sn.appTop.hom _)) = r
  rw [h4]
  simp

end GlobalTheory.ConstFn

theorem GlobalTheory.ConstFn.holoOn_univ_const : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim)
    (q : CxPts Y.str σ → ℂ), R.HoloOn Set.univ q → ∃ b : ℂ, ∀ z, q z = b := by
  intro F _ Y σ R q hq
  have hB := LB.isLB_triv Y.X
  have hs : (fun _ => q : (LB.triv Y.X).ι → CxPts Y.str σ → ℂ) ∈ R.holSec (LB.triv Y.X) := by
    refine ⟨⟨fun i j y hi _ => ?_, fun i y h => (h mem_ptsIn_top).elim⟩, fun i => hq.mono (Set.subset_univ _)⟩
    cases i; cases j
    rw [gv_self hB hi, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC Y.isProjOver R hB).2 ⟨_, hs⟩
  let M : Submodule ℂ ((LB.triv Y.X).ι → CxPts Y.str σ → ℂ) :=
    { carrier := {s | ∃ b : ℂ, ∀ i z, s i z = b}
      zero_mem' := ⟨0, fun _ _ => rfl⟩
      add_mem' := fun {s t} ⟨b, hb⟩ ⟨c, hc⟩ => ⟨b + c, fun i z => by simp [hb, hc]⟩
      smul_mem' := fun c s ⟨b, hb⟩ => ⟨c * b, fun i z => by simp [hb]⟩ }
  obtain ⟨b, hb⟩ : SecC.val x ∈ M := SecC.val_mem_of (fun s => by
    obtain ⟨b, hb⟩ := GlobalTheory.ConstFn.exists_ev_eq (p := Y.str) (σ := σ) (s.f PUnit.unit)
    exact ⟨b, fun i z => by cases i; exact hb z⟩) x
  refine ⟨b, fun z => ?_⟩
  have e := congrArg Subtype.val hx
  rw [AnRead.coe_valC] at e
  have := hb PUnit.unit z
  rw [e] at this
  exact this
