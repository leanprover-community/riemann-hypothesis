module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLatStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.UTraitRam

theorem evalZ_eq_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → φ.evalZ T'.be = m * φ.evalZ T.be := by
  intro E _ _ _ H Dw l Xo c _ T T' f fK hf hl hK hy m hm φ hφ
  obtain ⟨hdvr, hcpl, hz⟩ := T'.cdvr
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hz⟩
  have hself : Associated (RingHom.id T'.V T'.ϖ) (T'.ϖ ^ 1) := by simp [Associated.refl]
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices E H Dw l Xo c T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB hdvr hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    hself
  have hon : IsPolFanOn H.bar φ T.P.D.toPre.X := by
    haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
    exact hφ _ (GlobalTheory.UPoinc.UTrait.finrank_le_min E H Dw l Xo c T)
  have hc : toReal T.be ∈ psdCone (bar := H.bar) (X := T.P.D.toPre.X) :=
    GlobalTheory.PolFan.StrictData.toReal_mem_psdCone ((balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev)
      fun y => by simpa using T.mono.nonneg 0 y
  rw [← evalR_toReal φ T.be, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.UPoinc.UTraitRam
