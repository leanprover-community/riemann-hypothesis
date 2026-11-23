module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeOfIsAlgClosed
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.PieriBlockIdeals.BlockIdealBound5Derived
import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.PieriBlockIdeals.MertensReciprocalElementary
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published.CharAboveModel
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame.Tests

section Jumps

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]


variable (Ω) in
theorem exists_bridge (τ : E →+* Qbar l) : ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : IsPlaceOver A w)
    (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
      IsInduced Bw τ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := by
  first
  | exact @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | (apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge ..)

end Jumps


variable (l : ℕ) [Fact l.Prime]

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]


section Small

end Small

end GlobalTheory.ExpFrame.Tests

end
