module

public import Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfLocalCriterionAn
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def MuRootListProductOneSumEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (l : List (Prim q Γ(U, ⊤))), (l.map fun ζ => ζ.1).prod = 1 →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0

theorem mu_root_relation_submodule_etale_locally_zero_of_root_lists (h : MuRootListProductOneSumEtaleLocallyZero) : MuRootRelationSubmoduleEtaleLocallyZero := by
  intro q _ U x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact h q U l hl
  | zero => exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨S, hS, hSa⟩ := ha
    obtain ⟨T, hT, hTb⟩ := hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg.1
    have h2 : ((twF q 1).map g.appTop).hom b = 0 := hTb V g hg.2
    show ((twF q 1).map g.appTop).hom (a + b) = 0
    rw [map_add (f := _), h1, h2, add_zero]
  | smul c a _ ha =>
    obtain ⟨S, hS, hSa⟩ := ha
    exact ⟨S, hS, fun V g hg => by
      have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg
      show ((twF q 1).map g.appTop).hom (c • a) = 0
      rw [map_smul, h1, smul_zero]⟩

theorem exists_etale_mono_mu_twist_quotient_of_root_lists_locally_zero (h : MuRootListProductOneSumEtaleLocallyZero) : ExistsEtaleMonoMuTwistKillingRootRelations :=
  exists_etale_mono_muTwist_quotient_of_locally_zero etale_sheafify_mono_of_kernel_locally_zero (mu_root_relation_submodule_etale_locally_zero_of_root_lists h)

end LateralTheory.EtaleFoundations
