module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelGLengthConj
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

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.selG_length_eq_of_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (P : LocPrime l) (nb : ∀ w, w ∈ Formalism.BasicNotions.placesOver E l → LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) (A.1 w)) O) (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (k : ℕ) (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : GL (Fin k) O), (∀ g, M' g * (U : Matrix (Fin k) (Fin k) O) = (U : Matrix (Fin k) (Fin k) O) * M g) → Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M) = Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M') := by
  first | exact @GlobalTheory.SelConj.selG_length_conj | exact GlobalTheory.SelConj.selG_length_conj | (intros; apply GlobalTheory.SelConj.selG_length_conj <;> assumption)
