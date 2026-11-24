module

import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPfSec
public import Development.EtaleCohomology.TateTwists.TwLocPfR
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (hQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W h => Q W (h ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, h, g, hg, hh, rfl⟩
  exact hT' V g hg W h hh

theorem loc_surj {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : Sec (ofRings R M) U) :
    Loc U fun V g => ∃ x : M.obj Γ(V, ⊤), Sec.res g y = ofRings.sec M V x := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y
  refine ⟨_, h, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, hx.symm⟩

end LateralTheory.EtaleFoundations.TwSecLocPf

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def ZarPow : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)),
  Loc V fun W h => ∃ a : (ZMod q)ˣ, (ξ.map h.appTop.hom).1 = (ζ.map h.appTop.hom).1 ^ (a : ZMod q).val

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  apply LateralTheory.E.H2CurveOrder.TwLocGenPfSec.twF_single_pow <;> assumption

theorem twF_loc (hZ : ZarPow) (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤))
    (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
  apply LateralTheory.E.H2CurveOrder.TwLocGenPfSec.twF_loc <;> assumption

theorem TwSecLoc_of (hZ : ZarPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := by
  intro q _ i U ζ y
  refine loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_
  refine loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  have e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
    apply Subtype.ext
    simp [Prim.map]
    rfl
  rw [e]
  refine (congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_
  have hres : Sec.res h (ofRings.sec (twF q i) V x) =
      ofRings.sec (twF q i) W (((twF q i).map h.appTop).hom x) := by
    have hn := congrArg (fun f => f.hom x)
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality h.op)
    simp only [ModuleCat.hom_comp] at hn
    exact hn.symm
  refine hres.trans ?_
  rw [hc, ← hp]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

end LateralTheory.EtaleFoundations.TwSecLocPf
