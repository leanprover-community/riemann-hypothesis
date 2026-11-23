module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoMobCodiscreteWithinStatement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def germCompMob (g : GQ) : Mero →+* Mero where
  toFun F := F.compTendsto (mob g) (GlobalTheory.T.tendsto_mob_codiscreteWithin_codiscreteWithin g)
  map_one' := rfl
  map_mul' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl
  map_zero' := rfl
  map_add' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl

theorem germCompMob_coe (g : GQ) (φ : ℂ → ℂ) :
    germCompMob g (φ : Mero) = ((fun z => φ (mob g z)) : Mero) := rfl

theorem an_sl_germ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ) (f : T.K) (φ : ℂ → ℂ), T.an f = (φ : Mero) → T.an (T.sl g f) = ((fun z => φ (mob g z)) : Mero) := by
  intro Ω _ _ _ ε T g f φ hf
  have key : T.an.comp ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) = (germCompMob g).comp T.an := by
    apply (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1 Mero
    intro a
    obtain ⟨a', ha', hs⟩ := (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a
    simp only [RingHom.comp_apply]
    rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) (T.io a) = T.sl g (T.io a) from rfl, hs, T.an_io, T.an_io]
    unfold germ
    rw [germCompMob_coe]
    apply (GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict).2.2.1
    intro z hz
    rw [ha']
    exact (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz
  have h2 := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at h2
  rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) f = T.sl g f from rfl] at h2
  rw [h2, hf, germCompMob_coe]

end GlobalTheory.FN
