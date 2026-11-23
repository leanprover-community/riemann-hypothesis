module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KumRoots

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose R hR hRQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h V g (hSP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hR V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hRQ V g hg W k hk

abbrev unitsP : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ) := Scheme.Γ ⋙ unitsF

theorem unitSec_eq {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) :
    unitSec u = ((toSheafify Scheme.etaleTopology unitsP).app (op U)).hom (ULift.up (Additive.ofMul u)) := rfl

theorem res_unitSec {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology unitsP).naturality g.op)
    (ULift.up (Additive.ofMul u))
  exact this.symm

theorem unitSec_pow {U : Scheme.{0}} (q : ℕ) (v : (Γ(U, ⊤))ˣ) :
    unitSec (v ^ q) = Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) := by
  have h1 : (ULift.up (Additive.ofMul (v ^ q)) : unitsP.obj (op U)) = (q : ℤ) • ULift.up (Additive.ofMul v) := by
    apply ULift.ext
    change Additive.ofMul (v ^ q) = (q : ℤ) • Additive.ofMul v
    rw [natCast_zsmul, ofMul_pow]
  change _ = (q : ℤ) • unitSec v
  rw [unitSec_eq, unitSec_eq, h1]
  exact map_zsmul ((toSheafify Scheme.etaleTopology unitsP).app (op U)).hom (q : ℤ) _

end GlobalTheory.EtC.KumRoots

namespace GlobalTheory.EtC.KumRoots

theorem res_comp {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (x : Sec Gm U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change (Gm.obj.map (k ≫ g).op).hom x = (Gm.obj.map k.op).hom ((Gm.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem units_map_comp {X W U : Scheme.{0}} (k : X ⟶ W) (f : W ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ f).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map f.appTop.hom.toMonoidHom u) := by
  apply Units.ext
  change (k ≫ f).appTop.hom (u : Γ(U, ⊤)) = k.appTop.hom (f.appTop.hom u)
  rw [Scheme.Hom.comp_appTop]; rfl

theorem roots : ∀ (q : ℕ) [NeZero q],
    (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
      Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  intro q _ hyp U hq u
  refine loc_bind (hyp U hq (unitSec u)) ?_
  rintro V g ⟨c, hc⟩
  refine loc_bind (P := fun W h => ∃ v : (Γ(W, ⊤))ˣ, unitSec v = Sec.res h c)
    ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology unitsP) (U := op V) c, ?_⟩ ?_
  · rintro W h ⟨t, ht⟩
    exact ⟨Additive.toMul t.down, ht⟩
  · rintro W h ⟨v, hv⟩
    have heq : unitSec (v ^ q) = unitSec (Units.map (h ≫ g).appTop.hom.toMonoidHom u) :=
      calc unitSec (v ^ q) = Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) := unitSec_pow q v
        _ = Sec.map ((q : ℤ) • 𝟙 Gm) (Sec.res h c) := by rw [hv]
        _ = Sec.res h (Sec.map ((q : ℤ) • 𝟙 Gm) c) :=
          ConcreteCategory.congr_hom ((((q : ℤ) • 𝟙 Gm : Gm ⟶ Gm)).hom.naturality h.op) c
        _ = Sec.res h (Sec.res g (unitSec u)) := by rw [hc]
        _ = Sec.res (h ≫ g) (unitSec u) := (res_comp g h _).symm
        _ = unitSec (Units.map (h ≫ g).appTop.hom.toMonoidHom u) := res_unitSec _ _
    rw [unitSec_eq, unitSec_eq] at heq
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology unitsP)
      (X := op W) _ _ heq, ?_⟩
    intro X k hk
    have hk' : Units.map k.appTop.hom.toMonoidHom (v ^ q) =
        Units.map k.appTop.hom.toMonoidHom (Units.map (h ≫ g).appTop.hom.toMonoidHom u) :=
      congrArg (fun z : ULift.{1} (Additive (Γ(X, ⊤))ˣ) => Additive.toMul z.down) hk
    refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
    rw [← map_pow, hk', Category.assoc, units_map_comp k (h ≫ g)]

end GlobalTheory.EtC.KumRoots
