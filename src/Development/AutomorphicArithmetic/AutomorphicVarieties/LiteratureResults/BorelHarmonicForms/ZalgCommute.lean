module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
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

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

namespace UpperTheory.V.Lit.Bor.CasimirCentre

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem zalg_commute {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (o : Op E a) : Commute z (act o) := by
  refine Algebra.adjoin_induction (p := fun x _ => Commute x (act o)) ?_ (fun r => Algebra.commutes r _)
    (fun _ _ _ _ hx hy => hx.add_left hy) (fun _ _ _ _ hx hy => hx.mul_left hy) hz
  rintro _ ⟨τ, u, rfl⟩
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

private theorem uC_shift (r : ℝ) (X : Lie E a) : Cm.uC E a (shift (Cm.ιC E a) r X) = shift (lie E a) r X := by
  rw [shift_apply, shift_apply, map_add (f := _), Cm.uC_ιC, ← algebraMap_smul ℂ (r * ell E a X) (1 : Cm.UC E a), map_smul,
    map_one, algebraMap_smul]

private theorem center_of {z : Cm.UC E a} (h : ∀ X, Commute z (Cm.ιC E a X)) : z ∈ Subalgebra.center ℂ (Cm.UC E a) := by
  have hle : Algebra.adjoin ℂ {x : Cm.UC E a | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (((h _).sub_right ((h _).smul_right _)).smul_right _).eq
  rw [Cm.adjoin_genC] at hle
  exact Subalgebra.mem_center_iff.2 fun x => (hle Algebra.mem_top z rfl).symm

end UpperTheory.V.Lit.Bor.CasimirCentre

open UpperTheory.V.Lit.Bor.CasimirCentre in
theorem UpperTheory.V.Lit.Bor.casPi :
    UpperTheory.V.Lit.Bor.CasPi := by
  intro E _ _ _ a n e he π r
  have hL : IsLieHom (shift (Cm.ιC E a) r) := (ellFacts E a).2.2.2 _ _ r Cm.isLieHom_ιC
  have hc : cas (shift (Cm.ιC E a) r) e ∈ Subalgebra.center ℂ (Cm.UC E a) := center_of fun X => by
    have h := casComm E a n e he _ _ hL X
    have h' : Cm.ιC E a X = shift (Cm.ιC E a) r X - (r * ell E a X) • 1 := by rw [shift_apply, add_sub_cancel_right]
    rw [h']
    exact h.sub_right ((Commute.one_right _).smul_right _)
  have hz : cas (shift (lie E a) r) e ∈ Zalg E a := by
    rw [Cm.Zalg_eq_map]
    exact ⟨_, hc, by simp only [cas, map_sum, map_sub, map_mul, uC_shift, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩
  exact π.exists_scalar hz (zalg_commute hz)
