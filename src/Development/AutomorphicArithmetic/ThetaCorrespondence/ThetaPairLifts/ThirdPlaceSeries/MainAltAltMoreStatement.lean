module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltMore
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
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.fontaine_quotient_degrees_of_ptFam : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ := by
  first | exact @_root_.GlobalTheory.HubFon.main_alt_alt | exact _root_.GlobalTheory.HubFon.main_alt_alt | (intros; apply _root_.GlobalTheory.HubFon.main_alt_alt <;> assumption)
end
