module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.GalUnitaryO
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.AtLOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdAtLOf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.P
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin n) (Qbar l)} {w : Plc L} {τ : SmIrr (GLw n w)} {A : ValuationSubring Ω}
  {HT : (L →+* Qbar l) → Multiset ℤ}
theorem ordinary_at_l_of_local_global_hodge_tate_weights (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (h : IsPlaceOver A w) (lam : Wt L l n) (_ : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∃ τ, HtGT r HT w τ)
    (k : HtGT r HT w τ) (hL : LocGlobT ι r w τ)
    (hw : ∀ j : W.Emb l w, (HT (j.1.comp (algebraMap L _))).map (fun k : ℤ => (k : ℂ)) =
      (infOfWeight (lam (j.1.comp (algebraMap L _))).dual).map fun z => ((n : ℂ) - 1) / 2 - z) :
    Ord.AtLT ι h (r.comp (Dec (F := L) A).subtype) lam τ := _root_.UpperTheory.V.Z.Ord.at_l_of_literal_automorphy_n N l L Ω ι n A w h r HT τ lam k hL hw
end UpperTheory.V.Z.Desc.P
end
end
