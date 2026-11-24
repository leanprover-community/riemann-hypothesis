module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocLEqIntVOfDvdUnit
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

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop) (π c : 𝓞 E) (T : ℕ),
    (T : 𝓞 F) ∉ v.asIdeal → π * c = (T : 𝓞 E) →
    (∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) → ∀ (y : Fin n → E ⊗[F] v.adicCompletion F),
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  first | exact @GlobalTheory.locL_eq_intV_of_dvd_unit | exact GlobalTheory.locL_eq_intV_of_dvd_unit | (intros; apply GlobalTheory.locL_eq_intV_of_dvd_unit <;> assumption)
