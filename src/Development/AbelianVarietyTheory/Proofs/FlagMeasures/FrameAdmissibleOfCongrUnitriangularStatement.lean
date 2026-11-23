module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdmissibleOfCongrUnitriangular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

theorem _root_.GlobalTheory.T.frame_admissible_of_congr_unitriangular : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ), g ≠ 0 → ∀ {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → M a b = 0) → (∀ a, M a a = 1) → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a b, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * M a b = o) → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ b, ModG S Λ g (frame F' b - ∑ a, M a b • frame F a)) → IsAdmissible Λ g F F' := by
  first | exact @GlobalTheory.admissible_of_congr_unitriangular | exact GlobalTheory.admissible_of_congr_unitriangular | (intros; apply GlobalTheory.admissible_of_congr_unitriangular <;> assumption)
