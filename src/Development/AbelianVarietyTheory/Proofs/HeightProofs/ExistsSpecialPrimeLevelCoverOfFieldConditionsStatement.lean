module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpecialPrimeLevelCoverOfFieldConditions
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_specialPrime_levelCover_of_fieldConditions : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) := by
  first | exact @GlobalTheory.FinalJoin2.Cover.exists_cover_of_fieldOK | exact GlobalTheory.FinalJoin2.Cover.exists_cover_of_fieldOK | (intros; apply GlobalTheory.FinalJoin2.Cover.exists_cover_of_fieldOK <;> assumption)
