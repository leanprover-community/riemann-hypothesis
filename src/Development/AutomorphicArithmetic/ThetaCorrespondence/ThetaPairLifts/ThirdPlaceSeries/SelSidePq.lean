module

public import Formalism.LocalToGlobal.SelSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2
namespace SelJ
variable {D : D7} {X : Col.Fields}
end SelJ
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
def SelInAlt (R : _root_.Formalism.L2.RecTAlt ex) (Side : Set (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  ∀ μ, ∀ P ∈ Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K),
    ∀ P', SelJ.Carried R.T.ker.seam P P' → P' ∈ Side
def SelectedSideOfPrimeAbove (R : _root_.Formalism.L2.RecTAlt ex)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  (∀ v, NG.OverPl (Pq v) v) ∧ _root_.Formalism.L2.SelInAlt R (Set.range Pq)
end
end Formalism.L2
end
end
