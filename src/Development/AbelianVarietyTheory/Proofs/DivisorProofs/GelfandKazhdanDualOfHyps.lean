module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItselfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentreStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotPairedId
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_rapidDecay : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.CuspRapidDecaySiegelGL → GlobalTheory.Published.GelfandKazhdanDual := by
  intro hJS hAF hRD E _ _ _ n π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.Published.InvTransposeModel.rank_zero π
  · obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_twist_cuspidal_trivial_on_splitCentre E n hn π
    have hp := GlobalTheory.T.cusp_rep_paired_with_itself hJS.1 (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay hRD) hAF E n hn (π.twist χ) hχ
    have h := GlobalTheory.Published.InvTransposeModel.twist hp χ⁻¹
    rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GelfandKazhdanTop
