module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHomStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityCompRatAffineStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_sl_coeff_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (T : Frac Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : T.K) (r : ℚ) :
    (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) =
      eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  obtain ⟨hl, hmob⟩ := (GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties).2.2.2.2.2 g hg
  obtain ⟨_, hε, h0, hadd, _, _⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (RingHom.id Ω) (ent g 0 0 / ent g 1 1)
    (fun r => eOm ε (r * (ent g 0 1 / ent g 1 1))) hl (by simpa using h0)
    (fun r r' => by simp only [add_mul, hadd])
  have key : (T.exp.toRingHom.comp (T.sl g).toRingEquiv.toRingHom) = Φ.comp T.exp.toRingHom := by
    apply (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1
    intro a
    obtain ⟨a', ha', hsl⟩ := (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a
    have hE : IsExp ε a' (Φ (T.exp (T.io a))) := by
      refine GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine Ω ε a a' (ent g 0 0 / ent g 1 1) (ent g 0 1 / ent g 1 1) _ _ hl
        (fun z hz => ?_) (fun s => ?_) (T.exp_io a)
      · rw [ha', (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz, hmob z]
      · rw [hΦ, map_mul, hε]
        rfl
    have hu := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (T.exp_io a') hE
    show T.exp (T.sl g (T.io a)) = Φ (T.exp (T.io a))
    rw [hsl, hu]
  have hc := congrArg (fun h : HahnSeries ℚ Ω => h.coeff (r * (ent g 0 0 / ent g 1 1)))
    (RingHom.congr_fun key f)
  simp only [RingHom.comp_apply] at hc
  rw [mul_div_assoc, mul_div_assoc]
  refine (show (T.exp (T.sl g f)).coeff (r * (ent g 0 0 / ent g 1 1)) = _ from hc).trans ?_
  rw [hΦ]
  rfl

end GlobalTheory.FN
