module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKF

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

def LocUPairEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), PairOK B X W M om →
    M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) [LocallyCompactSpace (Fv F v)] [Invertible (2 : Fv F v)]
      [IsModuleTopology (Fv F v) (Ev E v)],
      ∃ ψv dv χXv χWv omv, IsLocPair M B.ψ χX χW om v ψv dv χXv χWv omv ∧
        IsUWeilPair (cV σ v) (sbClass (Fv F v)) ψv (-1) (locM X.J v) (locM W.J v) dv χXv χWv omv

end PositivityTheory.ThKF

end
