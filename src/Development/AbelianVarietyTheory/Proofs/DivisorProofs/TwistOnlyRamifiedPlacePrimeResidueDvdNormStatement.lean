module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistOnlyRamifiedPlacePrimeResidueDvdNorm
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

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

theorem _root_.GlobalTheory.T.twist_only_ramified_place_prime_residue_dvd_norm : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ q ∣ GlobalTheory.SqTop.Qn G t ∧ ∃ w' ∈ GlobalTheory.FunObj.locPl G t, Ideal.absNorm w'.asIdeal = q := by
  first | exact @GlobalTheory.SqTop.twist_ram_prime_dvd_Qn | exact GlobalTheory.SqTop.twist_ram_prime_dvd_Qn | (intros; apply GlobalTheory.SqTop.twist_ram_prime_dvd_Qn <;> assumption)
