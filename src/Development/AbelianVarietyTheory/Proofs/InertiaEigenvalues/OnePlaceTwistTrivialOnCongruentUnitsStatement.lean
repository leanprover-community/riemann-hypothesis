module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceTwistTrivialOnCongruentUnits
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.onePlaceTwist_trivial_on_congruent_units : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  first | exact @GlobalTheory.OnePlaceCong.chi_eq_one_of_cong | exact GlobalTheory.OnePlaceCong.chi_eq_one_of_cong | (intros; apply GlobalTheory.OnePlaceCong.chi_eq_one_of_cong <;> assumption)
