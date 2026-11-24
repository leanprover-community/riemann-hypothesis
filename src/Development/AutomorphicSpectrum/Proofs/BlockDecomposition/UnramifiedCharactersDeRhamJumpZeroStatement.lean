module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZero
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
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

theorem _root_.GlobalTheory.T.local_character_induced_agree : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ),
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) → (∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1) →
      ∀ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) →
      (∀ σ : ↥(Dec (F := E) A), (σ : G E Ω) ∈ V → (σ : G E Ω) ∈ Ine (F := E) A → ψ σ = 1) →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ 0 := by
  first | exact @GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | exact GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | (intros; apply GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia <;> assumption)
