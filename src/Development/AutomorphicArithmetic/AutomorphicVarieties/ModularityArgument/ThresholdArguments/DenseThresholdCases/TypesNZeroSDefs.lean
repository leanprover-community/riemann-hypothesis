module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroGDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
def Step_spCount_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) → (∀ i, res (c i) = res (G.chi i)) →
    FiniteDimensional ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ∧
      Module.finrank ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ≤ 1
def Step_spOrd_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) →
    ∀ σ : Equiv.Perm (Fin n), IsSubquotient π (prinSeries (fun i => c (σ i))) → IsSubquotient π (prinSeries c)
def Step_spPiSub_alt : Prop :=
  _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) → _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis →
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
    (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
    ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
    (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
    (multiProd G.e (G.twD τ)).IsIrreducible →
    IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries (G.cOf ν))
def Step_spSupp_alt : Prop :=
  _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) → _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
      ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
      (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsSubquotient π (prinSeries (G.cOf ν))
def Step_spTop_alt : Prop :=
  SpecialLatticeProp → G.SphericalVectorUniqueness → G.Step_spCount_alt → G.SpecialLiftProp → G.NonzeroBasicTwistOfSpecialForm → G.SpecialRestrictionProp → G.SpecialRepresentationEtaProp →
    _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) → G.Step_spPiSub_alt → G.Step_spSupp_alt → _root_.UpperTheory.TNZ.Step_cuspSupp_alt → _root_.UpperTheory.TNZ.Step_prodIrr_alt → TensorProductVectors →
    G.Step_suppProd_alt
end Grp
end UpperTheory.TNZ
end
end
