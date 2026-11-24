module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CloseOnCompletedLatticeOfCloseOnFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.close_on_completed_lattice_of_close_on_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (D : ℤ) (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV) (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep) (t : (A.loc p).Fp), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 → (∀ k l, ∃ o : 𝓞 E, (D : E) * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ k l = o) → (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * G.Hm a b * sig (Sum.elim G.f G.f' l b) = o) → (∀ l, (D : 𝓞 E) • Sum.elim G.f G.f' l ∈ Λ) → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ j, h (A.bc p (G.f' j)) = ∑ i, M' i j • A.bc p (G.f' i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → (∀ i j, ∃ o ∈ (A.L p).O, (M' - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
  first | exact @GlobalTheory.HL.LatClose.close_on_lattice | exact GlobalTheory.HL.LatClose.close_on_lattice | (intros; apply GlobalTheory.HL.LatClose.close_on_lattice <;> assumption)
