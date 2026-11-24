module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaPoint
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

@[expose] public section



section
noncomputable section
namespace GlobalTheory.ParamRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
section Twist
variable {Γ : Type} [Group Γ]
end Twist
end GlobalTheory.ParamRep
section Final
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
theorem GlobalTheory.ParamRep.jointCond_33_rho_of_signature_adm5 : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut → XiOverO D.nd D.naut → Formalism.MainNotions.N.GlobalDatumResidualRepCondition D := by
  intro D h0 h2 _ h5 h41 hGC hXi a x _ Sig hSig hgood
  exact _root_.GlobalTheory.ParamRep.rep_at_point_alt_alt D.nd D.naut h0.1 h0.2.1 (GlobalTheory.LocalInv.weightRegular_definite D) h2 h5 h41 hGC hXi
    a x Sig hSig hgood
end Final
end
end
