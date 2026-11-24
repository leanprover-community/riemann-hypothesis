module

public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open NumberField IsDedekindDomain Formalism.L2.Col

theorem _root_.GlobalTheory.T.exists_typePrime_under_eq : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)), ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  first | exact @GlobalTheory.GprimUnder.exists_vG_under | exact GlobalTheory.GprimUnder.exists_vG_under | (intros; apply GlobalTheory.GprimUnder.exists_vG_under <;> assumption)
