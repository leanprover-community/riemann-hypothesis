module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxFamLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyLinearEquivOfRel
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem mem_span_boxFam : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ S : Fam D'.toPre F k, S ∈ Submodule.span F {S' | ∃ s : Fin j → Fam D.toPre F k, IsBoxFam pD F k S' s} := by
  intro hL hL₂ _ _ V _ _ _ _ j D D' pD F _ _ k hk S
  obtain ⟨hf, hd⟩ := FamDimension.finrank_fam (D := D.toPre) (F := F) hL.globalFns hL₂.secTwist D.tau_bimult hk
  obtain ⟨hf', hd'⟩ := FamDimension.finrank_fam (D := D'.toPre) (F := F) hL.globalFns hL₂.secTwist D'.tau_bimult hk
  obtain ⟨hr, hg⟩ := rank_and_g_of_isPowDeg V j D.toPre D'.toPre pD
  let b := Module.finBasis F (Fam D.toPre F k)
  choose b' hb' using fun a : Fin j → Fin (Module.finrank F (Fam D.toPre F k)) =>
    BoxFamily.exists_isBoxFam hL.globalFns V j D.toPre D'.toPre pD F k (fun i => b (a i))
  have hi : LinearIndependent F b' :=
    boxFam_linearIndependent V j D.toPre D'.toPre pD F k _ b b.linearIndependent b' hb'
  have hc : Fintype.card (Fin j → Fin (Module.finrank F (Fam D.toPre F k))) =
      Module.finrank F (Fam D'.toPre F k) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hd, hd', hr, hg, ← pow_mul, ← mul_add, mul_comm]
  have ht : Submodule.span F (Set.range b') = ⊤ := hi.span_eq_top_of_card_eq_finrank' hc
  have hS : S ∈ Submodule.span F (Set.range b') := ht ▸ Submodule.mem_top
  refine Submodule.span_mono ?_ hS
  rintro _ ⟨a, rfl⟩
  exact ⟨_, hb' a⟩

end GlobalTheory
